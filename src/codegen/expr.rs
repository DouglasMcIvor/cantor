use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{
    ast::BinOp,
    error::CompileError,
    kind::Kind,
    semantics::tree::{SemExpr, SemExprKind},
    span::{Span, Symbol},
};

use super::expr_vec::vector_len_fn_name;
use super::overload_dispatch::CallTarget;
use super::{Compiler, Env};

impl<'ctx> Compiler<'ctx> {
    pub(crate) fn compile_expr(
        &self,
        expr: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        match &expr.kind {
            SemExprKind::IntLit(n) => match self.current_bare_int_kind() {
                Kind::Int64 => {
                    let v = self.context.i64_type().const_int(*n as u64, true);
                    Ok((v.into(), Kind::Int64))
                }
                _ => {
                    let v = self.compile_tagged_i64_const(*n)?;
                    Ok((v.into(), Kind::Int))
                }
            },
            SemExprKind::BoolLit(b) => {
                let v = self.context.bool_type().const_int(*b as u64, false);
                Ok((v.into(), Kind::Bool))
            }
            SemExprKind::Var(sym) => env.get(sym).map(|(v, t)| (*v, t.clone())).ok_or_else(|| {
                CompileError::UndefinedVariable {
                    name: sym.0.clone(),
                    span: expr.span,
                }
            }),
            SemExprKind::Add(lhs, rhs) => self.compile_arith(BinOp::Add, lhs, rhs, env, expr.span),
            SemExprKind::Sub(lhs, rhs) => self.compile_arith(BinOp::Sub, lhs, rhs, env, expr.span),
            SemExprKind::Mul(lhs, rhs) => self.compile_arith(BinOp::Mul, lhs, rhs, env, expr.span),
            SemExprKind::Div(lhs, rhs) => self.compile_arith(BinOp::Div, lhs, rhs, env, expr.span),
            // Set-position-only variants: elaboration never threads these into
            // a value-position tree (see `semantics::elaborate`'s module doc),
            // so reaching them here means an elaborator invariant broke —
            // fail loudly rather than guess.
            SemExprKind::DisjointUnion(..)
            | SemExprKind::SetDifference(..)
            | SemExprKind::CartesianProduct(..)
            | SemExprKind::SetQuotient(..)
            | SemExprKind::Comprehension { .. }
            | SemExprKind::KleeneStar(_) => Err(CompileError::ice(format!(
                "elaborator invariant broken: set-position node {:?} reached compile_expr \
                 (value position)",
                expr.kind
            ))),
            SemExprKind::UnOp { op, expr: inner } => self.compile_unop(*op, inner, env, expr.span),
            SemExprKind::BinOp { op, lhs, rhs } => {
                self.compile_binop(*op, lhs, rhs, env, expr.span)
            }
            SemExprKind::Call { callee, args } => self.compile_call(callee, args, env, expr.span),
            SemExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => self.compile_if(cond, then_expr, else_expr, env),
            SemExprKind::SetLit(elements) => self.compile_set_lit_value(elements, env),
            SemExprKind::Try(inner) => self.compile_try(inner, env),
            SemExprKind::FailLit => {
                // fail → {i1=1, i64=0}
                let zero = self.context.i64_type().const_int(0, false);
                let v = self.build_fail_struct(zero.into())?;
                Ok((v, Kind::Tuple(vec![Kind::Fail, Kind::Int])))
            }
            SemExprKind::FailWith(inner) => {
                // fail n → {i1=1, i64=n}
                let (v, _) = self.compile_expr(inner, env)?;
                let s = self.build_fail_struct(v)?;
                Ok((s, Kind::Tuple(vec![Kind::Fail, Kind::Int])))
            }
            SemExprKind::Tuple(elems) => self.compile_tuple(elems, env),
            SemExprKind::Proj { base, index } => self.compile_proj(base, *index, env),
            SemExprKind::Index { base, index } => self.compile_index(base, index, env),
        }
    }

    fn compile_try(
        &self,
        inner: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (val, _kind) = self.compile_expr(inner, env)?;

        if !val.is_struct_value() {
            return Err(CompileError::ice(
                "`?` applied to a non-fallible expression (expected `{i1, i64}` struct return)",
            ));
        }

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("`?` outside a function"))?;

        let struct_val = val.into_struct_value();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        // Extract the fail flag (field 0 = i1).
        let fail_flag = self
            .builder
            .build_extract_value(struct_val, 0, "try_flag")
            .map_err(err)?
            .into_int_value();

        // If fail_flag = 1: propagate — return the struct to the caller.
        // If fail_flag = 0: extract the i64 success payload and continue.
        let propagate_bb = self.context.append_basic_block(function, "try_fail");
        let success_bb = self.context.append_basic_block(function, "try_ok");
        self.builder
            .build_conditional_branch(fail_flag, propagate_bb, success_bb)
            .map_err(err)?;

        self.builder.position_at_end(propagate_bb);
        self.builder
            .build_return(Some(&inkwell::values::BasicValueEnum::StructValue(
                struct_val,
            )))
            .map_err(err)?;

        self.builder.position_at_end(success_bb);
        let payload = self
            .builder
            .build_extract_value(struct_val, 1, "try_payload")
            .map_err(err)?;

        Ok((payload, Kind::Int))
    }

    fn compile_if(
        &self,
        cond: &SemExpr,
        then_expr: &SemExpr,
        else_expr: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("if-then-else outside a function"))?;

        let (cond_val, _) = self.compile_expr(cond, env)?;
        let cond_i1 = cond_val.into_int_value();

        let then_bb = self.context.append_basic_block(function, "then");
        let else_bb = self.context.append_basic_block(function, "else");
        let merge_bb = self.context.append_basic_block(function, "merge");

        self.builder
            .build_conditional_branch(cond_i1, then_bb, else_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        self.builder.position_at_end(then_bb);
        let (then_val_raw, then_ty) = self.compile_expr(then_expr, env)?;
        let then_bb_cur = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(else_bb);
        let (else_val_raw, else_ty) = self.compile_expr(else_expr, env)?;
        let else_bb_cur = self.builder.get_insert_block().unwrap();

        // The Kind-level decision (what the merged Kind is, and which
        // coercion path gets there) is shared with the elaborator via
        // `kind::merge_if_branches` so the two can't silently disagree; only
        // the LLVM value construction below is codegen-specific.
        let merge =
            crate::kind::merge_if_branches(&then_ty, &else_ty).map_err(|e| CompileError::ice(e))?;

        let (then_val, else_val, result_ty) = match &merge {
            crate::kind::IfMerge::Same(_) => (then_val_raw, else_val_raw, then_ty),
            crate::kind::IfMerge::CoerceInt64ToInt => {
                self.builder.position_at_end(then_bb_cur);
                let tv = self
                    .ensure_tagged(then_val_raw.into_int_value(), &then_ty)?
                    .into();
                self.builder.position_at_end(else_bb_cur);
                let ev = self
                    .ensure_tagged(else_val_raw.into_int_value(), &else_ty)?
                    .into();
                (tv, ev, merge.result_kind())
            }
            crate::kind::IfMerge::CoerceToFailStruct => {
                self.builder.position_at_end(then_bb_cur);
                let tv = self.coerce_to_fail_struct(then_val_raw, &then_ty)?;
                self.builder.position_at_end(else_bb_cur);
                let ev = self.coerce_to_fail_struct(else_val_raw, &else_ty)?;
                (tv, ev, merge.result_kind())
            }
            crate::kind::IfMerge::NewTaggedUnion { arms } => {
                self.builder.position_at_end(then_bb_cur);
                let tv = self.build_tagged_union_value(0, then_val_raw, &then_ty, arms)?;
                self.builder.position_at_end(else_bb_cur);
                let ev = self.build_tagged_union_value(1, else_val_raw, &else_ty, arms)?;
                (tv, ev, merge.result_kind())
            }
            crate::kind::IfMerge::MergeTaggedUnions {
                merged_arms,
                else_remap,
            } => {
                let Kind::TaggedUnion(then_inner) = &then_ty else {
                    unreachable!("MergeTaggedUnions guarantees a TaggedUnion then-branch")
                };
                let Kind::TaggedUnion(else_inner) = &else_ty else {
                    unreachable!("MergeTaggedUnions guarantees a TaggedUnion else-branch")
                };

                self.builder.position_at_end(then_bb_cur);
                let tv = self.rewrap_tagged_union_value(then_val_raw, then_inner, merged_arms)?;

                self.builder.position_at_end(else_bb_cur);
                let old_struct = AggregateValueEnum::StructValue(else_val_raw.into_struct_value());
                let old_tag = self
                    .builder
                    .build_extract_value(old_struct, 0, "tu_merge_tag")
                    .map_err(|e| CompileError::ice(e.to_string()))?
                    .into_int_value();
                let new_tag = self.remap_tagged_union_tag(old_tag, else_remap)?;
                let ev = self.rewrap_tagged_union_with_tag(
                    else_val_raw,
                    else_inner,
                    merged_arms,
                    new_tag,
                )?;

                (tv, ev, merge.result_kind())
            }
            crate::kind::IfMerge::AppendElseArm { merged_arms } => {
                let Kind::TaggedUnion(inner_arms) = &then_ty else {
                    unreachable!("AppendElseArm guarantees a TaggedUnion then-branch")
                };
                let n = inner_arms.len();
                self.builder.position_at_end(then_bb_cur);
                let tv = self.rewrap_tagged_union_value(then_val_raw, inner_arms, merged_arms)?;
                self.builder.position_at_end(else_bb_cur);
                let ev = self.build_tagged_union_value(n, else_val_raw, &else_ty, merged_arms)?;
                (tv, ev, merge.result_kind())
            }
            crate::kind::IfMerge::AppendThenArm { merged_arms } => {
                let Kind::TaggedUnion(inner_arms) = &else_ty else {
                    unreachable!("AppendThenArm guarantees a TaggedUnion else-branch")
                };
                let n = inner_arms.len();
                self.builder.position_at_end(then_bb_cur);
                let tv = self.build_tagged_union_value(n, then_val_raw, &then_ty, merged_arms)?;
                self.builder.position_at_end(else_bb_cur);
                let ev = self.rewrap_tagged_union_value(else_val_raw, inner_arms, merged_arms)?;
                (tv, ev, merge.result_kind())
            }
        };

        // Emit unconditional branches and capture the ending blocks.
        self.builder.position_at_end(then_bb_cur);
        self.builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let then_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(else_bb_cur);
        self.builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let else_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(then_val.get_type(), "iftmp")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        phi.add_incoming(&[(&then_val, then_bb_end), (&else_val, else_bb_end)]);

        Ok((phi.as_basic_value(), result_ty))
    }

    /// Every binary operator except `+ - * /` (which are dedicated
    /// `SemExprKind` variants, see `compile_arith`) — comparisons, `and`/`or`,
    /// `in`/`not in`, `|`/`&`/`^`, and `++`.
    fn compile_binop(
        &self,
        op: BinOp,
        lhs: &SemExpr,
        rhs: &SemExpr,
        env: &Env<'ctx>,
        _span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        // Membership checks: only the LHS is a value; the RHS is a set expression.
        // When the RHS is a variable that resolves to a runtime set in env, dispatch
        // to the runtime contains function rather than the compile-time path.
        match op {
            BinOp::In | BinOp::NotIn => {
                let (lv, lk) = self.compile_expr(lhs, env)?;
                // int-soundness-plan phase 3 step 4b: `Kind::Int` is always
                // tagged, `Kind::Int64` always raw — `compile_membership`
                // needs to know which to interpret `lv` as.
                let tagged = lk == Kind::Int;
                let pred = if let Kind::TaggedUnion(ref arms) = lk {
                    // Tagged-union values: check the tag against the matching arm.
                    self.compile_tagged_union_membership(lv, arms, rhs)?
                } else if let SemExprKind::Var(sym) = &rhs.kind {
                    if let Some((set_ptr, Kind::Set(ek))) = env.get(sym) {
                        self.compile_runtime_contains(lv, lk, *set_ptr, ek)?
                    } else {
                        self.compile_membership(lv.into_int_value(), rhs, tagged)?
                    }
                } else {
                    self.compile_membership(lv.into_int_value(), rhs, tagged)?
                };
                if op == BinOp::NotIn {
                    let neg = self
                        .builder
                        .build_not(pred, "not_in")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    return Ok((neg.into(), Kind::Bool));
                }
                return Ok((pred.into(), Kind::Bool));
            }
            _ => {}
        }

        let (lv, lk) = self.compile_expr(lhs, env)?;
        let (rv, rk) = self.compile_expr(rhs, env)?;
        let li = self.scalarize_to_int(lv, &lk)?;
        let ri = self.scalarize_to_int(rv, &rk)?;
        let b = &self.builder;

        macro_rules! cmp_op {
            ($pred:ident, $name:literal) => {{
                let v = b
                    .build_int_compare(IntPredicate::$pred, li, ri, $name)
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                Ok((v.into(), Kind::Bool))
            }};
        }
        macro_rules! bool_op {
            ($method:ident, $name:literal) => {{
                let v = b
                    .$method(li, ri, $name)
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                Ok((v.into(), Kind::Bool))
            }};
        }

        // int-soundness-plan phase 3 step 4b: a comparison between two
        // genuinely raw `Kind::Int64` operands stays a plain `icmp` below;
        // anything touching a tagged `Kind::Int` operand routes through
        // `cantor_bigint_cmp` instead — a raw i64 bit-pattern comparison is
        // meaningless once either side could be a boxed pointer.
        let both_int64 = lk == Kind::Int64 && rk == Kind::Int64;
        let both_int_like =
            matches!(lk, Kind::Int | Kind::Int64) && matches!(rk, Kind::Int | Kind::Int64);
        // `both_int_like` only ever holds for the six comparison operators —
        // `And`/`Or` operate on `Kind::Bool` operands, and every other `op`
        // reaching this point operates on `Set`/`Vector` kinds, never `Int`.
        let tagged_pred = match op {
            BinOp::Eq => Some(IntPredicate::EQ),
            BinOp::Ne => Some(IntPredicate::NE),
            BinOp::Lt => Some(IntPredicate::SLT),
            BinOp::Le => Some(IntPredicate::SLE),
            BinOp::Gt => Some(IntPredicate::SGT),
            BinOp::Ge => Some(IntPredicate::SGE),
            _ => None,
        };
        if let Some(pred) = tagged_pred
            && self.tagging_active()
            && both_int_like
            && !both_int64
        {
            let li = self.ensure_tagged(li, &lk)?;
            let ri = self.ensure_tagged(ri, &rk)?;
            let cmp_fn = self
                .module
                .get_function("cantor_bigint_cmp")
                .ok_or_else(|| CompileError::ice("cantor_bigint_cmp not declared"))?;
            let cmp = self
                .builder
                .build_call(cmp_fn, &[li.into(), ri.into()], "bigint_cmp")
                .map_err(|e| CompileError::ice(e.to_string()))?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice("cantor_bigint_cmp returned void"))?
                .into_int_value();
            let zero = self.context.i64_type().const_int(0, true);
            let v = self
                .builder
                .build_int_compare(pred, cmp, zero, "bigint_cmp_result")
                .map_err(|e| CompileError::ice(e.to_string()))?;
            return Ok((v.into(), Kind::Bool));
        }

        match op {
            BinOp::Eq => cmp_op!(EQ, "eq"),
            BinOp::Ne => cmp_op!(NE, "ne"),
            BinOp::Lt => cmp_op!(SLT, "lt"),
            BinOp::Le => cmp_op!(SLE, "le"),
            BinOp::Gt => cmp_op!(SGT, "gt"),
            BinOp::Ge => cmp_op!(SGE, "ge"),
            BinOp::And => bool_op!(build_and, "and"),
            BinOp::Or => bool_op!(build_or, "or"),
            BinOp::In | BinOp::NotIn => unreachable!("handled above"),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => unreachable!(
                "Add/Sub/Mul/Div are dedicated SemExprKind variants, never wrapped in BinOp"
            ),
            BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
                Err(CompileError::ice("set operations not yet implemented"))
            }
            BinOp::Concat => self.compile_vec_concat(lhs, rhs, env, _span),
        }
    }

    fn compile_vec_concat(
        &self,
        lhs: &SemExpr,
        rhs: &SemExpr,
        env: &Env<'ctx>,
        _span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (lv, lk) = self.compile_expr(lhs, env)?;
        let (rv, rk) = self.compile_expr(rhs, env)?;

        // The Kind-level decision (does either side's literal Tuple need
        // coercing into a Vector, and what's the resulting element Kind) is
        // shared with the elaborator via `kind::merge_concat_kinds`, so the
        // two can't silently disagree; only the LLVM value construction
        // below is codegen-specific.
        let (mode, result_kind) = crate::kind::merge_concat_kinds(&lk, &rk)
            .map_err(|e| CompileError::ice(format!("{e} at {_span:?}")))?;
        let elem_kind = match &result_kind {
            Kind::Vector(ek) => ek.as_ref().clone(),
            _ => unreachable!("merge_concat_kinds always returns a Vector result Kind"),
        };

        let (lv, _lk) = match mode {
            crate::kind::ConcatMerge::CoerceLhsToVector => {
                let Kind::Tuple(elems) = &lk else {
                    unreachable!("CoerceLhsToVector guarantees a Tuple lhs")
                };
                let elems = elems.clone();
                self.compile_tuple_as_vector(lv, &elems, &elem_kind)?
            }
            _ => (lv, lk),
        };
        let (rv, _rk) = match mode {
            crate::kind::ConcatMerge::CoerceRhsToVector => {
                let Kind::Tuple(elems) = &rk else {
                    unreachable!("CoerceRhsToVector guarantees a Tuple rhs")
                };
                let elems = elems.clone();
                self.compile_tuple_as_vector(rv, &elems, &elem_kind)?
            }
            _ => (rv, rk),
        };

        let concat_fn = match &elem_kind {
            Kind::Int => "cantor_vec_concat_i64",
            Kind::Bool => "cantor_vec_concat_bool",
            Kind::Vector(_) => "cantor_list_vec_concat",
            Kind::Tuple(_) => "cantor_struct_vec_concat",
            Kind::TaggedUnion(_) => "cantor_union_vec_concat",
            other => {
                return Err(CompileError::ice(format!(
                    "TODO: `++` not yet implemented for element kind {other:?}"
                )));
            }
        };

        let fn_val = self.module.get_function(concat_fn).ok_or_else(|| {
            CompileError::ice(format!("runtime function `{concat_fn}` not declared"))
        })?;
        let lv_i64 = lv.into_int_value();
        let rv_i64 = rv.into_int_value();
        let result = self
            .builder
            .build_call(fn_val, &[lv_i64.into(), rv_i64.into()], "concat")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let result_i64 = result.try_as_basic_value().left().ok_or_else(|| {
            CompileError::ice(format!("`{concat_fn}` returned void unexpectedly"))
        })?;
        Ok((result_i64, Kind::Vector(Box::new(elem_kind))))
    }

    fn compile_call(
        &self,
        callee: &Symbol,
        args: &[SemExpr],
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        // `from(x)` — built-in destructor for `distinct` values; identity at
        // runtime. Preserves the argument's actual Kind (Int or Int64,
        // whichever it already is) rather than hardcoding — it's a pure
        // pass-through, not a fresh value.
        if callee.0 == "from" && args.len() == 1 {
            let (val, kind) = self.compile_expr(&args[0], env)?;
            return Ok((val, kind));
        }

        // Auto-generated constructor `d(x)` for `D = distinct B`; identity at
        // runtime — same reasoning as `from(x)` above.
        if args.len() == 1 {
            let mut chars = callee.0.chars();
            if let Some(first) = chars.next() {
                let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
                if self.distinct_names.contains(&capitalized) {
                    let (val, kind) = self.compile_expr(&args[0], env)?;
                    return Ok((val, kind));
                }
            }
        }

        // `size(s)` — built-in cardinality function for runtime sets.
        if callee.0 == "size" && args.len() == 1 {
            let (ptr, kind) = self.compile_expr(&args[0], env)?;
            let size_fn = match &kind {
                // Cardinality is representation-agnostic (every backing
                // struct is a plain `Vec<i64>` under the hood, tagged or
                // not), so the raw-vs-tagged split that `contains`/`for`
                // need doesn't matter here.
                Kind::Set(elem) if **elem == Kind::Bool => "cantor_set_size_bool",
                Kind::Set(_) => "cantor_set_size_i64",
                _ => return Err(CompileError::ice("size() requires a runtime set argument")),
            };
            let fn_val = self
                .module
                .get_function(size_fn)
                .ok_or_else(|| CompileError::ice(format!("{size_fn} not declared")))?;
            let result = self
                .builder
                .build_call(fn_val, &[ptr.into()], "size")
                .map_err(|e| CompileError::ice(e.to_string()))?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice("size fn returned void"))?;
            // int-soundness-plan phase 3 step 4b: `cantor_set_size_i64`
            // returns a raw i64 count, but this builtin's result is an
            // ordinary `Kind::Int` (tagged) value like any other — tag it.
            let result = self
                .ensure_tagged(result.into_int_value(), &Kind::Int64)?
                .into();
            return Ok((result, Kind::Int));
        }

        // `len(xs)` — built-in length function for vectors (Kind::Vector).
        if callee.0 == "len" && args.len() == 1 {
            let (ptr, kind) = self.compile_expr(&args[0], env)?;
            return match &kind {
                Kind::Vector(ek) => {
                    let len_fn = vector_len_fn_name(ek)?;

                    let fn_val = self
                        .module
                        .get_function(len_fn)
                        .ok_or_else(|| CompileError::ice(format!("{len_fn} not declared")))?;
                    let result = self
                        .builder
                        .build_call(fn_val, &[ptr.into()], "len")
                        .map_err(|e| CompileError::ice(e.to_string()))?
                        .try_as_basic_value()
                        .left()
                        .ok_or_else(|| CompileError::ice("len fn returned void"))?;
                    // int-soundness-plan phase 3 step 4b: same reasoning as
                    // `size()` above — the runtime function returns a raw
                    // count, tag it before it's used as a `Kind::Int` value.
                    let result = self
                        .ensure_tagged(result.into_int_value(), &Kind::Int64)?
                        .into();
                    Ok((result, Kind::Int))
                }
                Kind::Tuple(inner_eks) => {
                    let length = Vec::len(inner_eks);
                    let v = self.compile_tagged_i64_const(length as i64)?;
                    Ok((v.into(), Kind::Int))
                }
                _ => Err(CompileError::ice("len() requires a vector (X*) argument")),
            };
        }

        // int-soundness-plan phase 2: overload dispatch. Absent from
        // `overload_dispatch` ⇒ today's plain path, unchanged (the
        // overwhelming common case). Present ⇒ resolve which candidate(s)
        // this call's arity admits, then either a direct call (arity alone,
        // or a solver-proved resolution, picked exactly one) or a runtime
        // membership-test dispatch chain.
        let (lookup_key, target) = self.resolve_overload_call_target(callee, args, span)?;

        // int-soundness-plan phase 3 step 4b: an unresolved dispatch call
        // must present every candidate a *common* representation to test
        // membership against and to `phi`-merge results from — that common
        // representation is the tagged `Kind::Int` (never raw `Kind::Int64`,
        // which has no tag bit to represent "whichever candidate wins"
        // generically). `lookup_key`'s own declared kinds might be the
        // `Int64` half of a compiler-generated split (file order pushes it
        // first), so a real `Direct` call still uses the callee's exact
        // declared kinds unchanged, but a `Dispatch` call canonicalizes any
        // `Int64` position to `Int` here — `compile_overload_dispatch`
        // decodes back down to each individual candidate's real kind right
        // before calling it.
        let param_kinds_for_callee = self.fn_param_kinds.get(&lookup_key).map(|ks| {
            if matches!(target, CallTarget::Dispatch(_)) {
                ks.iter()
                    .map(|k| {
                        if *k == Kind::Int64 {
                            Kind::Int
                        } else {
                            k.clone()
                        }
                    })
                    .collect()
            } else {
                ks.clone()
            }
        });
        let mut compiled_arg_values = Vec::with_capacity(args.len());
        for (arg_idx, arg) in args.iter().enumerate() {
            let (v, arg_kind) = self.compile_expr(arg, env)?;
            let expected_kind = param_kinds_for_callee
                .as_deref()
                .and_then(|ks| ks.get(arg_idx));

            // When the callee expects a Vector but we have a scalar or tuple,
            // box it into a singleton/flat Arrow vector (sequence unification).
            let (v, arg_kind) = if let Some(Kind::Vector(ek)) = expected_kind {
                if !matches!(arg_kind, Kind::Vector(_)) {
                    let ek = ek.as_ref().clone();
                    match &arg_kind {
                        Kind::Int | Kind::Bool => {
                            self.compile_scalar_as_singleton_vector(v, &arg_kind, &ek)?
                        }
                        Kind::Tuple(elems) => {
                            let elems = elems.clone();
                            self.compile_tuple_as_vector(v, &elems, &ek)?
                        }
                        _ => (v, arg_kind),
                    }
                } else {
                    (v, arg_kind)
                }
            } else {
                (v, arg_kind)
            };

            // When the callee expects (or doesn't expect) a TaggedUnion param —
            // e.g. a `+`-typed domain like `{0} + NatPos` — but the argument's
            // Kind disagrees, widen/narrow it. Mirrors `coerce_tagged_union_return`
            // at the call boundary instead of the return boundary; see
            // `coerce_call_arg` for why this needs the callee's recorded domain
            // set expression to disambiguate same-Kind `+` arms.
            let (v, arg_kind) = match expected_kind {
                Some(expected @ Kind::TaggedUnion(_))
                    if !matches!(arg_kind, Kind::TaggedUnion(_)) =>
                {
                    self.coerce_call_arg(v, arg_kind, expected, &lookup_key, arg_idx)?
                }
                Some(expected)
                    if matches!(arg_kind, Kind::TaggedUnion(_))
                        && !matches!(expected, Kind::TaggedUnion(_)) =>
                {
                    self.coerce_call_arg(v, arg_kind, expected, &lookup_key, arg_idx)?
                }
                _ => (v, arg_kind),
            };

            // int-soundness-plan phase 3 step 4b: tag/untag at the call
            // boundary when the argument's representation doesn't match
            // what the callee (or, for a dispatch call, the canonical
            // shared representation — see above) declares — e.g. an
            // ordinary tagged local passed into a `Kind::Int64` parameter,
            // or a Step-A-promoted call's raw result passed into an
            // ordinary tagged one.
            let (v, arg_kind) = match expected_kind {
                Some(Kind::Int64) if arg_kind == Kind::Int => (
                    self.ensure_raw_int64(v.into_int_value(), &arg_kind)?.into(),
                    Kind::Int64,
                ),
                Some(Kind::Int) if arg_kind == Kind::Int64 => (
                    self.ensure_tagged(v.into_int_value(), &arg_kind)?.into(),
                    Kind::Int,
                ),
                _ => (v, arg_kind),
            };

            // All function parameters are i64 (uniform ABI); widen Bool args.
            let v_i64 = if arg_kind == Kind::Bool {
                self.builder
                    .build_int_z_extend(v.into_int_value(), self.context.i64_type(), "arg_bool_ext")
                    .map_err(|e| CompileError::ice(e.to_string()))?
                    .into()
            } else {
                v
            };
            compiled_arg_values.push(v_i64);
        }
        let compiled_args: Vec<_> = compiled_arg_values.iter().map(|&v| v.into()).collect();
        let is_dispatch = matches!(target, CallTarget::Dispatch(_));

        let result_i64 = match target {
            CallTarget::Direct(name) => {
                let function = self.module.get_function(&name).ok_or_else(|| {
                    CompileError::UndefinedVariable {
                        name: callee.0.clone(),
                        span,
                    }
                })?;
                let call = self
                    .builder
                    .build_call(function, &compiled_args, "call")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                call.try_as_basic_value()
                    .left()
                    .ok_or_else(|| CompileError::ice("void return in expression position"))?
            }
            CallTarget::Dispatch(candidates) => self.compile_overload_dispatch(
                &callee.0,
                &candidates,
                &compiled_arg_values,
                param_kinds_for_callee.as_deref().unwrap_or(&[]),
                span,
            )?,
        };

        // Restore the correct Kind after the call. For a `Dispatch` call,
        // `compile_overload_dispatch` already normalizes every candidate's
        // result to the canonical tagged `Int` before its `phi` merge (see
        // that function), so the call-site result here is `Int`, never
        // whichever candidate `lookup_key` happened to name.
        let raw_return_kind = self
            .fn_return_kinds
            .get(&lookup_key)
            .cloned()
            .unwrap_or(Kind::Int);
        let return_kind = if is_dispatch && raw_return_kind == Kind::Int64 {
            Kind::Int
        } else {
            raw_return_kind
        };
        match &return_kind {
            Kind::Bool => {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        result_i64.into_int_value(),
                        self.context.bool_type(),
                        "call_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                Ok((i1_val.into(), Kind::Bool))
            }
            // Tuples and TaggedUnions are returned as struct values directly.
            // Union is i64 at this stage but we preserve the Kind for future stages.
            Kind::Tuple(_) | Kind::TaggedUnion(_) => Ok((result_i64, return_kind)),
            // Vector is an i64 pointer — pass through and preserve the Kind.
            Kind::Vector(_) | Kind::Set(_) => Ok((result_i64, return_kind)),
            // int-soundness-plan phase 3 step 4b: preserve the callee's real
            // declared Kind (`Int` vs raw `Int64`) instead of hardcoding
            // `Int` — a call into a Step-A-promoted or step-4a-split-Int64
            // function returns a raw word, and mislabelling it `Int` here
            // would make every downstream consumer treat it as tagged.
            _ => Ok((result_i64, return_kind)),
        }
    }

    /// Compile `{ e1, e2, … }` in value position into a heap-allocated runtime set.
    ///
    /// All elements must have the same Kind (homogeneous sets only for now).
    /// Returns a pointer-as-i64 with `Kind::Set(elem_kind)`.
    fn compile_set_lit_value(
        &self,
        elements: &[SemExpr],
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        if elements.is_empty() {
            return Err(CompileError::ice(
                "empty set literal in value position — element kind cannot be inferred; \
                 add an explicit annotation (e.g. `s : Set(Int) = {}`)",
            ));
        }

        let i64t = self.context.i64_type();

        // Compile all elements up front to determine and check homogeneity.
        let compiled: Vec<(BasicValueEnum<'ctx>, Kind)> = elements
            .iter()
            .map(|e| self.compile_expr(e, env))
            .collect::<Result<_, _>>()?;

        let elem_kind = compiled[0].1.clone();
        for (_, k) in &compiled {
            if *k != elem_kind {
                return Err(CompileError::ice(
                    "mixed element kinds in set literal — \
                     heterogeneous sets not yet supported",
                ));
            }
        }

        // `Kind::Int` under `tagging_active()` can carry a boxed element, which
        // needs magnitude-aware (not raw bit-pattern) dedup/ordering — see
        // `CantorTaggedIntSet`'s doc comment. `Kind::Int64` is always raw
        // (never boxed by construction) and stays on the plain path even when
        // tagging is active elsewhere in the program. `Bool`/`Fail` are both
        // wire-`i1`, always 0/1-valued, so they share the same bool-backed
        // runtime pair. Anything else isn't a legal `Set(_)` element kind —
        // `kind::is_scalar_word_kind` already rejects it during elaboration,
        // so reaching here is a compiler bug, not a user-reachable gap.
        let int_is_tagged = elem_kind == Kind::Int && self.tagging_active();
        let (new_fn, insert_fn) = match &elem_kind {
            Kind::Int if int_is_tagged => {
                ("cantor_tagged_set_new_i64", "cantor_tagged_set_insert_i64")
            }
            Kind::Int | Kind::Int64 => ("cantor_set_new_i64", "cantor_set_insert_i64"),
            Kind::Bool | Kind::Fail => ("cantor_set_new_bool", "cantor_set_insert_bool"),
            other => {
                return Err(CompileError::ice(format!(
                    "Set({other:?}) is not a legal runtime set element kind"
                )));
            }
        };

        // Allocate an empty set.
        let new_fn_val = self.module.get_function(new_fn).ok_or_else(|| {
            CompileError::ice(format!(
                "{new_fn} not declared — was declare_runtime_functions called?"
            ))
        })?;
        let ptr = self
            .builder
            .build_call(new_fn_val, &[], "new_set")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_set_new returned void"))?;

        // Insert each element (insert functions return void).
        let insert_fn_val = self.module.get_function(insert_fn).ok_or_else(|| {
            CompileError::ice(format!(
                "{insert_fn} not declared — was declare_runtime_functions called?"
            ))
        })?;
        for (val, k) in compiled {
            let val_i64: BasicValueEnum = if matches!(k, Kind::Bool | Kind::Fail) {
                self.builder
                    .build_int_z_extend(val.into_int_value(), i64t, "elem_bool_ext")
                    .map_err(|e| CompileError::ice(e.to_string()))?
                    .into()
            } else if k == Kind::Int && !int_is_tagged {
                // Not routed through the tagged set (either `Kind::Int64`, or
                // `Kind::Int` with tagging inactive program-wide) — decode to
                // the plain raw-ordered set's expected representation.
                self.ensure_raw_int64(val.into_int_value(), &k)?.into()
            } else {
                val
            };
            self.builder
                .build_call(insert_fn_val, &[ptr.into(), val_i64.into()], "insert")
                .map_err(|e| CompileError::ice(e.to_string()))?;
        }

        Ok((ptr, Kind::Set(Box::new(elem_kind))))
    }

    /// Compile `(e0, e1, …)` into an LLVM struct value.
    fn compile_tuple(
        &self,
        elems: &[SemExpr],
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let compiled: Vec<(BasicValueEnum<'ctx>, Kind)> = elems
            .iter()
            .map(|e| self.compile_expr(e, env))
            .collect::<Result<_, _>>()?;

        let elem_kinds: Vec<Kind> = compiled.iter().map(|(_, k)| k.clone()).collect();
        let llvm_types: Vec<_> = elem_kinds
            .iter()
            .map(|k| self.kind_to_llvm_type(k))
            .collect();
        let struct_type = self.context.struct_type(&llvm_types, false);

        let mut agg: AggregateValueEnum<'ctx> = struct_type.get_undef().into();
        for (i, (val, _)) in compiled.into_iter().enumerate() {
            agg = self
                .builder
                .build_insert_value(agg, val, i as u32, "tf")
                .map_err(|e| CompileError::ice(e.to_string()))?;
        }

        Ok((agg.into_struct_value().into(), Kind::Tuple(elem_kinds)))
    }
}
