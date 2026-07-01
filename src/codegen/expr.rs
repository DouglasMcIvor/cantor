use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{
    ast::{BinOp, UnOp},
    error::CompileError,
    kind::{Kind, SetElemKind},
    semantics::tree::{SemExpr, SemExprKind},
    span::{Span, Symbol},
};

use super::{Compiler, Env};


impl<'ctx> Compiler<'ctx> {
    pub(crate) fn compile_expr(
        &self,
        expr: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        match &expr.kind {
            SemExprKind::IntLit(n) => {
                let v = self.context.i64_type().const_int(*n as u64, true);
                Ok((v.into(), Kind::Int))
            }
            SemExprKind::BoolLit(b) => {
                let v = self.context.bool_type().const_int(*b as u64, false);
                Ok((v.into(), Kind::Bool))
            }
            SemExprKind::Var(sym) => env
                .get(sym)
                .map(|(v, t)| (*v, t.clone()))
                .ok_or_else(|| CompileError::UndefinedVariable {
                    name: sym.0.clone(),
                    span: expr.span,
                }),
            SemExprKind::Add(lhs, rhs) => self.compile_arith(BinOp::Add, lhs, rhs, env),
            SemExprKind::Sub(lhs, rhs) => self.compile_arith(BinOp::Sub, lhs, rhs, env),
            SemExprKind::Mul(lhs, rhs) => self.compile_arith(BinOp::Mul, lhs, rhs, env),
            SemExprKind::Div(lhs, rhs) => self.compile_arith(BinOp::Div, lhs, rhs, env),
            // Set-position-only variants: elaboration never threads these into
            // a value-position tree (see `semantics::elaborate`'s module doc),
            // so reaching them here means an elaborator invariant broke —
            // fail loudly rather than guess.
            SemExprKind::DisjointUnion(..)
            | SemExprKind::SetDifference(..)
            | SemExprKind::CartesianProduct(..)
            | SemExprKind::SetQuotient(..)
            | SemExprKind::Comprehension { .. }
            | SemExprKind::KleeneStar(_) => Err(CompileError::Internal(format!(
                "elaborator invariant broken: set-position node {:?} reached compile_expr \
                 (value position)", expr.kind
            ))),
            SemExprKind::UnOp { op, expr: inner } => self.compile_unop(*op, inner, env, expr.span),
            SemExprKind::BinOp { op, lhs, rhs } => self.compile_binop(*op, lhs, rhs, env, expr.span),
            SemExprKind::Call { callee, args } => self.compile_call(callee, args, env, expr.span),
            SemExprKind::If { cond, then_expr, else_expr } => {
                self.compile_if(cond, then_expr, else_expr, env)
            }
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

    /// Value-position `+ - * /` — dedicated `SemExprKind` variants (never
    /// wrapped in `BinOp`, see `tree.rs`'s module doc), always plain i64 arithmetic.
    fn compile_arith(
        &self,
        op: BinOp,
        lhs: &SemExpr,
        rhs: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (lv, lk) = self.compile_expr(lhs, env)?;
        let (rv, rk) = self.compile_expr(rhs, env)?;
        let li = self.scalarize_to_int(lv, &lk)?;
        let ri = self.scalarize_to_int(rv, &rk)?;
        let b = &self.builder;
        let v = match op {
            BinOp::Add => b.build_int_add(li, ri, "add"),
            BinOp::Sub => b.build_int_sub(li, ri, "sub"),
            BinOp::Mul => b.build_int_mul(li, ri, "mul"),
            BinOp::Div => b.build_int_signed_div(li, ri, "div"),
            _ => unreachable!("compile_arith is only called for Add/Sub/Mul/Div"),
        }
        .map_err(|e| CompileError::Internal(e.to_string()))?;
        Ok((v.into(), Kind::Int))
    }

    fn compile_try(
        &self,
        inner: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (val, _kind) = self.compile_expr(inner, env)?;

        if !val.is_struct_value() {
            return Err(CompileError::Internal(
                "`?` applied to a non-fallible expression (expected `{i1, i64}` struct return)"
                    .into(),
            ));
        }

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::Internal("`?` outside a function".into()))?;

        let struct_val = val.into_struct_value();
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());

        // Extract the fail flag (field 0 = i1).
        let fail_flag = self.builder
            .build_extract_value(struct_val, 0, "try_flag")
            .map_err(err)?
            .into_int_value();

        // If fail_flag = 1: propagate — return the struct to the caller.
        // If fail_flag = 0: extract the i64 success payload and continue.
        let propagate_bb = self.context.append_basic_block(function, "try_fail");
        let success_bb   = self.context.append_basic_block(function, "try_ok");
        self.builder
            .build_conditional_branch(fail_flag, propagate_bb, success_bb)
            .map_err(err)?;

        self.builder.position_at_end(propagate_bb);
        self.builder.build_return(Some(&inkwell::values::BasicValueEnum::StructValue(struct_val))).map_err(err)?;

        self.builder.position_at_end(success_bb);
        let payload = self.builder
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
            .ok_or_else(|| CompileError::Internal("if-then-else outside a function".into()))?;

        let (cond_val, _) = self.compile_expr(cond, env)?;
        let cond_i1 = cond_val.into_int_value();

        let then_bb  = self.context.append_basic_block(function, "then");
        let else_bb  = self.context.append_basic_block(function, "else");
        let merge_bb = self.context.append_basic_block(function, "merge");

        self.builder
            .build_conditional_branch(cond_i1, then_bb, else_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

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
        let merge = crate::kind::merge_if_branches(&then_ty, &else_ty)
            .map_err(CompileError::Internal)?;

        let (then_val, else_val, result_ty) = match &merge {
            crate::kind::IfMerge::Same(_) => (then_val_raw, else_val_raw, then_ty),
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
            crate::kind::IfMerge::MergeTaggedUnions { merged_arms, else_remap } => {
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
                let old_tag = self.builder
                    .build_extract_value(old_struct, 0, "tu_merge_tag")
                    .map_err(|e| CompileError::Internal(e.to_string()))?
                    .into_int_value();
                let new_tag = self.remap_tagged_union_tag(old_tag, else_remap)?;
                let ev = self.rewrap_tagged_union_with_tag(else_val_raw, else_inner, merged_arms, new_tag)?;

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
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let then_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(else_bb_cur);
        self.builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let else_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(then_val.get_type(), "iftmp")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        phi.add_incoming(&[(&then_val, then_bb_end), (&else_val, else_bb_end)]);

        Ok((phi.as_basic_value(), result_ty))
    }

    fn compile_unop(
        &self,
        op: UnOp,
        inner: &SemExpr,
        env: &Env<'ctx>,
        _span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (val, _ty) = self.compile_expr(inner, env)?;
        let iv = val.into_int_value();
        match op {
            UnOp::Neg => {
                let v = self
                    .builder
                    .build_int_neg(iv, "neg")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), Kind::Int))
            }
            // build_not is bitwise NOT; on i1 this is logical NOT (0↔1).
            UnOp::Not => {
                let v = self
                    .builder
                    .build_not(iv, "not")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), Kind::Bool))
            }
        }
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
                let pred = if let Kind::TaggedUnion(ref arms) = lk {
                    // Tagged-union values: check the tag against the matching arm.
                    self.compile_tagged_union_membership(lv, arms, rhs)?
                } else if let SemExprKind::Var(sym) = &rhs.kind {
                    if let Some(&(set_ptr, Kind::Set(ek))) = env.get(sym) {
                        self.compile_runtime_contains(lv, lk, set_ptr, ek)?
                    } else {
                        self.compile_membership(lv.into_int_value(), rhs)?
                    }
                } else {
                    self.compile_membership(lv.into_int_value(), rhs)?
                };
                if op == BinOp::NotIn {
                    let neg = self.builder.build_not(pred, "not_in")
                        .map_err(|e| CompileError::Internal(e.to_string()))?;
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
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), Kind::Bool))
            }};
        }
        macro_rules! bool_op {
            ($method:ident, $name:literal) => {{
                let v = b
                    .$method(li, ri, $name)
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), Kind::Bool))
            }};
        }

        match op {
            BinOp::Eq  => cmp_op!(EQ,  "eq"),
            BinOp::Ne  => cmp_op!(NE,  "ne"),
            BinOp::Lt  => cmp_op!(SLT, "lt"),
            BinOp::Le  => cmp_op!(SLE, "le"),
            BinOp::Gt  => cmp_op!(SGT, "gt"),
            BinOp::Ge  => cmp_op!(SGE, "ge"),
            BinOp::And => bool_op!(build_and, "and"),
            BinOp::Or  => bool_op!(build_or,  "or"),
            BinOp::In | BinOp::NotIn => unreachable!("handled above"),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => unreachable!(
                "Add/Sub/Mul/Div are dedicated SemExprKind variants, never wrapped in BinOp"
            ),
            BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
                Err(CompileError::Internal("set operations not yet implemented".into()))
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
            .map_err(|e| CompileError::Internal(format!("{e} at {_span:?}")))?;
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
            Kind::Int    => "cantor_vec_concat_i64",
            Kind::Bool   => "cantor_vec_concat_bool",
            Kind::Vector(_) => "cantor_list_vec_concat",
            Kind::Tuple(_)  => "cantor_struct_vec_concat",
            Kind::TaggedUnion(_) => "cantor_union_vec_concat",
            other => return Err(CompileError::Internal(format!(
                "TODO: `++` not yet implemented for element kind {other:?}"
            ))),
        };

        let fn_val = self.module.get_function(concat_fn).ok_or_else(|| {
            CompileError::Internal(format!("runtime function `{concat_fn}` not declared"))
        })?;
        let lv_i64 = lv.into_int_value();
        let rv_i64 = rv.into_int_value();
        let result = self.builder.build_call(fn_val, &[lv_i64.into(), rv_i64.into()], "concat")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let result_i64 = result.try_as_basic_value().left().ok_or_else(|| {
            CompileError::Internal(format!("`{concat_fn}` returned void unexpectedly"))
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
        // `from(x)` — built-in destructor for `distinct` values; identity at runtime.
        if callee.0 == "from" && args.len() == 1 {
            let (val, _kind) = self.compile_expr(&args[0], env)?;
            return Ok((val, Kind::Int));
        }

        // Auto-generated constructor `d(x)` for `D = distinct B`; identity at runtime.
        if args.len() == 1 {
            let mut chars = callee.0.chars();
            if let Some(first) = chars.next() {
                let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
                if self.distinct_names.contains(&capitalized) {
                    let (val, _kind) = self.compile_expr(&args[0], env)?;
                    return Ok((val, Kind::Int));
                }
            }
        }

        // `size(s)` — built-in cardinality function for runtime sets.
        if callee.0 == "size" && args.len() == 1 {
            let (ptr, kind) = self.compile_expr(&args[0], env)?;
            let size_fn = match kind {
                Kind::Set(SetElemKind::Int)  => "cantor_set_size_i64",
                Kind::Set(SetElemKind::Bool) => "cantor_set_size_bool",
                _ => return Err(CompileError::Internal(
                    "size() requires a runtime set argument".into(),
                )),
            };
            let fn_val = self.module.get_function(size_fn)
                .ok_or_else(|| CompileError::Internal(format!("{size_fn} not declared")))?;
            let result = self.builder
                .build_call(fn_val, &[ptr.into()], "size")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::Internal("size fn returned void".into()))?;
            return Ok((result, Kind::Int));
        }

        // `len(xs)` — built-in length function for vectors (Kind::Vector).
        if callee.0 == "len" && args.len() == 1 {
            let (ptr, kind) = self.compile_expr(&args[0], env)?;
            return match &kind {
                Kind::Vector(ek) => {
                    let len_fn = match ek.as_ref() {
                        Kind::Int  => "cantor_vec_len_i64",
                        Kind::Bool => "cantor_vec_len_bool",
                        Kind::Vector(_) => "cantor_list_vec_len",
                        Kind::Tuple(_) => "cantor_struct_vec_len",
                        Kind::TaggedUnion(_) => "cantor_union_vec_len",
                        other => return Err(CompileError::Internal(format!(
                            "len() on Vector({other:?}) not yet supported"
                        ))),
                    };

                    let fn_val = self.module.get_function(len_fn)
                        .ok_or_else(|| CompileError::Internal(format!("{len_fn} not declared")))?;
                    let result = self.builder
                        .build_call(fn_val, &[ptr.into()], "len")
                        .map_err(|e| CompileError::Internal(e.to_string()))?
                        .try_as_basic_value()
                        .left()
                        .ok_or_else(|| CompileError::Internal("len fn returned void".into()))?;
                    Ok((result, Kind::Int))
                },
                Kind::Tuple(inner_eks) => {
                    let length = Vec::len(inner_eks);
                    let v = self.context.i64_type().const_int(length as u64, true);
                    Ok((v.into(), Kind::Int))
                },
                _ => Err(CompileError::Internal(
                    "len() requires a vector (X*) argument".into(),
                )),
            };
        }

        let function = self.module.get_function(&callee.0).ok_or_else(|| {
            CompileError::UndefinedVariable { name: callee.0.clone(), span }
        })?;

        let param_kinds_for_callee = self.fn_param_kinds.get(&callee.0).cloned();
        let mut compiled_args = Vec::with_capacity(args.len());
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
                Some(expected @ Kind::TaggedUnion(_)) if !matches!(arg_kind, Kind::TaggedUnion(_)) => {
                    self.coerce_call_arg(v, arg_kind, expected, &callee.0, arg_idx)?
                }
                Some(expected) if matches!(arg_kind, Kind::TaggedUnion(_)) && !matches!(expected, Kind::TaggedUnion(_)) => {
                    self.coerce_call_arg(v, arg_kind, expected, &callee.0, arg_idx)?
                }
                _ => (v, arg_kind),
            };

            // All function parameters are i64 (uniform ABI); widen Bool args.
            let v_i64 = if arg_kind == Kind::Bool {
                self.builder
                    .build_int_z_extend(
                        v.into_int_value(),
                        self.context.i64_type(),
                        "arg_bool_ext",
                    )
                    .map_err(|e| CompileError::Internal(e.to_string()))?
                    .into()
            } else {
                v
            };
            compiled_args.push(v_i64.into());
        }

        let call = self
            .builder
            .build_call(function, &compiled_args, "call")
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        let result_i64 = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("void return in expression position".into()))?;

        // Restore the correct Kind after the call.
        let return_kind = self.fn_return_kinds.get(&callee.0).cloned().unwrap_or(Kind::Int);
        match &return_kind {
            Kind::Bool => {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        result_i64.into_int_value(),
                        self.context.bool_type(),
                        "call_bool",
                    )
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((i1_val.into(), Kind::Bool))
            }
            // Tuples and TaggedUnions are returned as struct values directly.
            // Union is i64 at this stage but we preserve the Kind for future stages.
            Kind::Tuple(_) | Kind::TaggedUnion(_) => Ok((result_i64, return_kind)),
            // Vector is an i64 pointer — pass through and preserve the Kind.
            Kind::Vector(_) | Kind::Set(_) => Ok((result_i64, return_kind)),
            _ => Ok((result_i64, Kind::Int)),
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
            return Err(CompileError::Internal(
                "empty set literal in value position — element kind cannot be inferred; \
                 add an explicit annotation (e.g. `s : Set(Int) = {}`)"
                    .into(),
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
                return Err(CompileError::Internal(
                    "mixed element kinds in set literal — \
                     heterogeneous sets not yet supported"
                        .into(),
                ));
            }
        }

        let (set_elem_kind, new_fn, insert_fn) = match &elem_kind {
            Kind::Int  => (SetElemKind::Int,  "cantor_set_new_i64",  "cantor_set_insert_i64"),
            Kind::Bool => (SetElemKind::Bool, "cantor_set_new_bool", "cantor_set_insert_bool"),
            Kind::Set(_) => return Err(CompileError::Internal(
                "sets of sets not yet supported".into(),
            )),
            Kind::Fail | Kind::Tuple(_) | Kind::TaggedUnion(_) => return Err(CompileError::Internal(
                "sets of fail/tuples/unions not yet supported".into(),
            )),
            Kind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in codegen"),
        };

        // Allocate an empty set.
        let new_fn_val = self.module.get_function(new_fn)
            .ok_or_else(|| CompileError::Internal(
                format!("{new_fn} not declared — was declare_runtime_functions called?"),
            ))?;
        let ptr = self.builder
            .build_call(new_fn_val, &[], "new_set")
            .map_err(|e| CompileError::Internal(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("cantor_set_new returned void".into()))?;

        // Insert each element (insert functions return void).
        let insert_fn_val = self.module.get_function(insert_fn)
            .ok_or_else(|| CompileError::Internal(
                format!("{insert_fn} not declared — was declare_runtime_functions called?"),
            ))?;
        for (val, k) in compiled {
            let val_i64: BasicValueEnum = if k == Kind::Bool {
                self.builder
                    .build_int_z_extend(val.into_int_value(), i64t, "elem_bool_ext")
                    .map_err(|e| CompileError::Internal(e.to_string()))?
                    .into()
            } else {
                val
            };
            self.builder
                .build_call(insert_fn_val, &[ptr.into(), val_i64.into()], "insert")
                .map_err(|e| CompileError::Internal(e.to_string()))?;
        }

        Ok((ptr, Kind::Set(set_elem_kind)))
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
        let llvm_types: Vec<_> = elem_kinds.iter().map(|k| self.kind_to_llvm_type(k)).collect();
        let struct_type = self.context.struct_type(&llvm_types, false);

        let mut agg: AggregateValueEnum<'ctx> = struct_type.get_undef().into();
        for (i, (val, _)) in compiled.into_iter().enumerate() {
            agg = self.builder
                .build_insert_value(agg, val, i as u32, "tf")
                .map_err(|e| CompileError::Internal(e.to_string()))?;
        }

        Ok((agg.into_struct_value().into(), Kind::Tuple(elem_kinds)))
    }

}
