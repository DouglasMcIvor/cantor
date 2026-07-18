use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{
    ast::BinOp,
    error::CompileError,
    kind::Kind,
    semantics::tree::{SemExpr, SemExprKind},
    span::Span,
};

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
            SemExprKind::CharLit(c) => {
                let v = self.context.i32_type().const_int(*c as u32 as u64, false);
                Ok((v.into(), Kind::Char))
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
            SemExprKind::BinOp {
                op: op @ (BinOp::Rem | BinOp::Quot),
                lhs,
                rhs,
            } => self.compile_rem_quot(*op, lhs, rhs, env, expr.span),
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
                // fail → {tag=1, i64=0}
                let zero = self.context.i64_type().const_int(0, false);
                let v = self.build_fail_struct(zero.into())?;
                Ok((v, Kind::Tuple(vec![Kind::Fail, Kind::Int])))
            }
            SemExprKind::FailWith(inner) => {
                // fail n → {tag=1, i64=n}
                let (v, _) = self.compile_expr(inner, env)?;
                let s = self.build_fail_struct(v)?;
                Ok((s, Kind::Tuple(vec![Kind::Fail, Kind::Int])))
            }
            SemExprKind::NoneLit => {
                // none → {tag=2, i64=0}
                let s = self.build_none_struct()?;
                Ok((s, Kind::Tuple(vec![Kind::None, Kind::Int])))
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
                "`?` applied to a non-fallible expression (expected `{tag, i64}` struct return)",
            ));
        }

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("`?` outside a function"))?;

        let struct_val = val.into_struct_value();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        // Extract the tag (field 0 = i8: 0 success, 1 Fail, 2 None) and test
        // for "not success" — propagation doesn't care which of the two
        // non-zero tags fired, only that the whole struct passes through
        // unchanged (the tag and payload already carry the right meaning).
        let tag = self
            .builder
            .build_extract_value(struct_val, 0, "try_tag")
            .map_err(err)?
            .into_int_value();
        let zero_i8 = self.context.i8_type().const_int(0, false);
        let is_propagate = self
            .builder
            .build_int_compare(IntPredicate::NE, tag, zero_i8, "try_propagate")
            .map_err(err)?;

        // If is_propagate: propagate — return the struct to the caller.
        // If not: extract the i64 success payload and continue.
        let propagate_bb = self.context.append_basic_block(function, "try_fail");
        let success_bb = self.context.append_basic_block(function, "try_ok");
        self.builder
            .build_conditional_branch(is_propagate, propagate_bb, success_bb)
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
            crate::kind::IfMerge::AppendElseArm {
                merged_arms,
                else_tag,
            } => {
                let Kind::TaggedUnion(inner_arms) = &then_ty else {
                    unreachable!("AppendElseArm guarantees a TaggedUnion then-branch")
                };
                self.builder.position_at_end(then_bb_cur);
                let tv = self.rewrap_tagged_union_value(then_val_raw, inner_arms, merged_arms)?;
                self.builder.position_at_end(else_bb_cur);
                let ev =
                    self.build_tagged_union_value(*else_tag, else_val_raw, &else_ty, merged_arms)?;
                (tv, ev, merge.result_kind())
            }
            crate::kind::IfMerge::AppendThenArm {
                merged_arms,
                then_tag,
            } => {
                let Kind::TaggedUnion(inner_arms) = &else_ty else {
                    unreachable!("AppendThenArm guarantees a TaggedUnion else-branch")
                };
                self.builder.position_at_end(then_bb_cur);
                let tv =
                    self.build_tagged_union_value(*then_tag, then_val_raw, &then_ty, merged_arms)?;
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
            // `++` operands are vectors (or literal Tuples being coerced to
            // one) — never the `{i1, i64}`-shaped values `scalarize_to_int`
            // below assumes, so this must dispatch before that call, exactly
            // like `In`/`NotIn` above.
            BinOp::Concat => return self.compile_vec_concat(lhs, rhs, env, _span),
            _ => {}
        }

        let (lv, lk) = self.compile_expr(lhs, env)?;
        let (rv, rk) = self.compile_expr(rhs, env)?;
        let li = self.scalarize_to_int(lv, &lk)?;
        let ri = self.scalarize_to_int(rv, &rk)?;
        let b = &self.builder;

        // Unsigned32 (docs/wrapping-and-quotient-sets-plan.md): the one
        // place signed-vs-unsigned actually changes which LLVM predicate is
        // used. `Signed32` needs no special case — the default signed
        // predicates below (`SLT`/`SLE`/`SGT`/`SGE`) are already correct for
        // it, and `==`/`!=` never care about signedness either way.
        if lk == Kind::Unsigned32 {
            let pred = match op {
                BinOp::Eq => IntPredicate::EQ,
                BinOp::Ne => IntPredicate::NE,
                BinOp::Lt => IntPredicate::ULT,
                BinOp::Le => IntPredicate::ULE,
                BinOp::Gt => IntPredicate::UGT,
                BinOp::Ge => IntPredicate::UGE,
                _ => {
                    return Err(CompileError::ice(format!(
                        "`{op}` on Unsigned32 reached codegen — the solver should have \
                         already rejected this at compile time"
                    )));
                }
            };
            let v = b
                .build_int_compare(pred, li, ri, "u32cmp")
                .map_err(|e| CompileError::ice(e.to_string()))?;
            return Ok((v.into(), Kind::Bool));
        }

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
            BinOp::Rem | BinOp::Quot => unreachable!(
                "Rem/Quot are routed to compile_rem_quot by compile_expr's dispatch, \
                 never reach compile_binop"
            ),
            BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
                Err(CompileError::ice("set operations not yet implemented"))
            }
            BinOp::Concat => unreachable!("handled above, before scalarize_to_int"),
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

        use crate::kind::ConcatMerge;
        let (lv, _lk) = match mode {
            ConcatMerge::CoerceLhsToVector | ConcatMerge::CoerceBothToVector => {
                let Kind::Tuple(elems) = &lk else {
                    unreachable!("CoerceLhsToVector/CoerceBothToVector guarantees a Tuple lhs")
                };
                let elems = elems.clone();
                self.compile_tuple_as_vector(lv, &elems, &elem_kind)?
            }
            _ => (lv, lk),
        };
        let (rv, _rk) = match mode {
            ConcatMerge::CoerceRhsToVector | ConcatMerge::CoerceBothToVector => {
                let Kind::Tuple(elems) = &rk else {
                    unreachable!("CoerceRhsToVector/CoerceBothToVector guarantees a Tuple rhs")
                };
                let elems = elems.clone();
                self.compile_tuple_as_vector(rv, &elems, &elem_kind)?
            }
            _ => (rv, rk),
        };

        let concat_fn = match &elem_kind {
            Kind::Int | Kind::Char => "cantor_vec_concat_i64",
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
