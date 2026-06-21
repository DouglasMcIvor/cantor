use std::collections::HashMap;

use inkwell::{
    IntPredicate,
    values::BasicValueEnum,
};

use crate::{
    ast::{BinOp, Expr, ExprKind, UnOp},
    error::CompileError,
    kind::{Kind, SetElemKind},
    span::{Span, Symbol},
};

use super::{Compiler, Env, FAIL_SENTINEL, range_contains_fail};

/// Collect the pre-expanded integer-value lists for all user-defined named sets
/// that appear in a range union.  `Fail` and built-in sets (Nat, Int, Bool, …)
/// are ignored — only sets present in `user_set_vals` are returned.
fn collect_named_error_vals(range: &Expr, user_set_vals: &HashMap<String, Vec<i64>>) -> Vec<Vec<i64>> {
    match &range.kind {
        ExprKind::Var(sym) => {
            if sym.0 == "Fail" {
                return vec![];
            }
            if let Some(vals) = user_set_vals.get(sym.0.as_str()) {
                return vec![vals.clone()];
            }
            vec![]
        }
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            let mut sets = collect_named_error_vals(lhs, user_set_vals);
            sets.extend(collect_named_error_vals(rhs, user_set_vals));
            sets
        }
        _ => vec![],
    }
}

/// Collect value lists for error sets declared via `!!` (error-union operator).
///
/// For `Success !! ErrorSet`, the RHS is walked like a union of named sets.
/// The values are raw error codes; `compile_try` encodes them as
/// `FAIL_SENTINEL + code + 1` for the comparison, and decodes on match.
fn collect_error_union_vals(range: &Expr, user_set_vals: &HashMap<String, Vec<i64>>) -> Vec<Vec<i64>> {
    match &range.kind {
        ExprKind::BinOp { op: BinOp::ErrorUnion, rhs, .. } => {
            // RHS is the error set: may be a single named set or a union of named sets.
            collect_named_error_vals(rhs, user_set_vals)
        }
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            let mut sets = collect_error_union_vals(lhs, user_set_vals);
            sets.extend(collect_error_union_vals(rhs, user_set_vals));
            sets
        }
        _ => vec![],
    }
}

impl<'ctx> Compiler<'ctx> {
    pub(crate) fn compile_expr(
        &self,
        expr: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        match &expr.kind {
            ExprKind::IntLit(n) => {
                let v = self.context.i64_type().const_int(*n as u64, true);
                Ok((v.into(), Kind::Int))
            }
            ExprKind::BoolLit(b) => {
                let v = self.context.bool_type().const_int(*b as u64, false);
                Ok((v.into(), Kind::Bool))
            }
            ExprKind::Var(sym) => env
                .get(sym)
                .map(|&(v, t)| (v, t))
                .ok_or_else(|| CompileError::UndefinedVariable {
                    name: sym.0.clone(),
                    span: expr.span,
                }),
            ExprKind::UnOp { op, expr: inner } => self.compile_unop(*op, inner, env, expr.span),
            ExprKind::BinOp { op, lhs, rhs } => self.compile_binop(*op, lhs, rhs, env, expr.span),
            ExprKind::Call { callee, args } => self.compile_call(callee, args, env, expr.span),
            ExprKind::If { cond, then_expr, else_expr } => {
                self.compile_if(cond, then_expr, else_expr, env)
            }
            ExprKind::SetLit(elements) => self.compile_set_lit_value(elements, env),
            ExprKind::Comprehension { .. } => Err(CompileError::Internal(
                "comprehension in value position not yet supported".into(),
            )),
            ExprKind::Try(inner) => self.compile_try(inner, env),
            ExprKind::FailLit => {
                let sentinel = self.context.i64_type().const_int(FAIL_SENTINEL as u64, true);
                Ok((sentinel.into(), Kind::Int))
            }
            ExprKind::FailWith(inner) => {
                let (v, _) = self.compile_expr(inner, env)?;
                let n = v.into_int_value();
                let i64t = self.context.i64_type();
                // fail n → FAIL_SENTINEL + n + 1 (offset-encoded so 400 != fail 400)
                let base = i64t.const_int(FAIL_SENTINEL.wrapping_add(1) as u64, true);
                let encoded = self.builder
                    .build_int_add(base, n, "fail_encoded")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((encoded.into(), Kind::Int))
            }
        }
    }

    fn compile_try(
        &self,
        inner: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (val, _) = self.compile_expr(inner, env)?;
        let result_i64 = val.into_int_value();

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::Internal("`?` outside a function".into()))?;

        let i64_type = self.context.i64_type();

        // Determine error-checking strategy from the callee's declared range.
        // When `?` wraps a non-Call expression (unusual) we fall back to the
        // Fail-sentinel check so existing behaviour is preserved.
        let callee_range: Option<&Expr> = if let ExprKind::Call { callee, .. } = &inner.kind {
            self.fn_ranges.get(&callee.0)
        } else {
            None
        };

        let check_fail = callee_range
            .map(range_contains_fail)
            .unwrap_or(true); // fallback: assume Fail when range is unknown

        let named_error_sets: Vec<Vec<i64>> = callee_range
            .map(|r| collect_named_error_vals(r, &self.user_set_vals))
            .unwrap_or_default();

        // Raw error codes from `!!` error-union ranges (encoded as FAIL_SENTINEL + n + 1).
        let error_union_sets: Vec<Vec<i64>> = callee_range
            .map(|r| collect_error_union_vals(r, &self.user_set_vals))
            .unwrap_or_default();

        if !check_fail && named_error_sets.is_empty() && error_union_sets.is_empty() {
            return Err(CompileError::Internal(
                "`?` used on a callee whose range contains no `Fail` and no named \
                 error set — the callee cannot fail; remove `?`"
                    .into(),
            ));
        }

        // ── 1. Fail-sentinel check (for `| Fail` and `!!` callees) ──
        // `!!` callees can also return bare FAIL_SENTINEL from assert failures.
        if check_fail {
            let Some(fail_bb) = self.fail_bb else {
                return Err(CompileError::Internal(
                    "`?` propagates `Fail` but the current function does not declare \
                     `| Fail` or `!!` in its range"
                        .into(),
                ));
            };

            let sentinel = i64_type.const_int(FAIL_SENTINEL as u64, true);
            let is_fail = self
                .builder
                .build_int_compare(IntPredicate::EQ, result_i64, sentinel, "is_fail")
                .map_err(|e| CompileError::Internal(e.to_string()))?;

            let after_fail_bb = self
                .context
                .append_basic_block(function, "try_after_fail");
            self.builder
                .build_conditional_branch(is_fail, fail_bb, after_fail_bb)
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            self.builder.position_at_end(after_fail_bb);
        }

        // ── 2. Named error-set checks (`| HTTPError`): value returned unchanged ──
        for vals in &named_error_sets {
            let is_error = self.build_int_set_membership(result_i64, vals)?;

            let err_ret_bb = self
                .context
                .append_basic_block(function, "try_named_err");
            let next_bb = self
                .context
                .append_basic_block(function, "try_after_named");

            self.builder
                .build_conditional_branch(is_error, err_ret_bb, next_bb)
                .map_err(|e| CompileError::Internal(e.to_string()))?;

            // On error: return the error value to the caller immediately.
            self.builder.position_at_end(err_ret_bb);
            let ret_val: BasicValueEnum<'ctx> = result_i64.into();
            self.builder
                .build_return(Some(&ret_val))
                .map_err(|e| CompileError::Internal(e.to_string()))?;

            self.builder.position_at_end(next_bb);
        }

        // ── 3. Error-union checks (`!! HTTPError`): decode FAIL_SENTINEL+n+1 → n ──
        // The base constant is FAIL_SENTINEL + 1; decoding is `result - base`.
        let eu_base = i64_type.const_int(FAIL_SENTINEL.wrapping_add(1) as u64, true);
        for raw_vals in &error_union_sets {
            // Compute the encoded sentinel value for each raw error code.
            let encoded_vals: Vec<i64> = raw_vals
                .iter()
                .map(|&n| FAIL_SENTINEL.wrapping_add(n).wrapping_add(1))
                .collect();
            let is_error = self.build_int_set_membership(result_i64, &encoded_vals)?;

            let err_ret_bb = self.context.append_basic_block(function, "try_eu_err");
            let next_bb   = self.context.append_basic_block(function, "try_eu_after");

            self.builder
                .build_conditional_branch(is_error, err_ret_bb, next_bb)
                .map_err(|e| CompileError::Internal(e.to_string()))?;

            // On error: decode the payload (result - base) and return it.
            self.builder.position_at_end(err_ret_bb);
            let decoded = self.builder
                .build_int_sub(result_i64, eu_base, "eu_decoded")
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            let ret_val: BasicValueEnum<'ctx> = decoded.into();
            self.builder
                .build_return(Some(&ret_val))
                .map_err(|e| CompileError::Internal(e.to_string()))?;

            self.builder.position_at_end(next_bb);
        }

        // Success path lands here.
        let ok_bb = self.context.append_basic_block(function, "try_ok");
        self.builder
            .build_unconditional_branch(ok_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        self.builder.position_at_end(ok_bb);

        Ok((result_i64.into(), Kind::Int))
    }

    fn compile_if(
        &self,
        cond: &Expr,
        then_expr: &Expr,
        else_expr: &Expr,
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
        let (then_val, then_ty) = self.compile_expr(then_expr, env)?;
        self.builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let then_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(else_bb);
        let (else_val, _else_ty) = self.compile_expr(else_expr, env)?;
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

        Ok((phi.as_basic_value(), then_ty))
    }

    fn compile_unop(
        &self,
        op: UnOp,
        inner: &Expr,
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

    fn compile_binop(
        &self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        env: &Env<'ctx>,
        _span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        // Membership checks: only the LHS is a value; the RHS is a set expression.
        // When the RHS is a variable that resolves to a runtime set in env, dispatch
        // to the runtime contains function rather than the compile-time path.
        match op {
            BinOp::In | BinOp::NotIn => {
                let (lv, lk) = self.compile_expr(lhs, env)?;
                let pred = if let ExprKind::Var(sym) = &rhs.kind {
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

        let (lv, _) = self.compile_expr(lhs, env)?;
        let (rv, _) = self.compile_expr(rhs, env)?;
        let li = lv.into_int_value();
        let ri = rv.into_int_value();
        let b = &self.builder;

        macro_rules! int_op {
            ($method:ident, $name:literal) => {{
                let v = b
                    .$method(li, ri, $name)
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), Kind::Int))
            }};
        }
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
            BinOp::Add => int_op!(build_int_add, "add"),
            BinOp::Sub => int_op!(build_int_sub, "sub"),
            BinOp::Mul => int_op!(build_int_mul, "mul"),
            BinOp::Div => int_op!(build_int_signed_div, "div"),
            BinOp::Eq  => cmp_op!(EQ,  "eq"),
            BinOp::Ne  => cmp_op!(NE,  "ne"),
            BinOp::Lt  => cmp_op!(SLT, "lt"),
            BinOp::Le  => cmp_op!(SLE, "le"),
            BinOp::Gt  => cmp_op!(SGT, "gt"),
            BinOp::Ge  => cmp_op!(SGE, "ge"),
            BinOp::And => bool_op!(build_and, "and"),
            BinOp::Or  => bool_op!(build_or,  "or"),
            BinOp::In | BinOp::NotIn => unreachable!("handled above"),
            BinOp::Union | BinOp::ErrorUnion | BinOp::Intersect | BinOp::SymDiff => {
                Err(CompileError::Internal("set operations not yet implemented".into()))
            }
        }
    }

    fn compile_call(
        &self,
        callee: &Symbol,
        args: &[Expr],
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
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

        let function = self.module.get_function(&callee.0).ok_or_else(|| {
            CompileError::UndefinedVariable { name: callee.0.clone(), span }
        })?;

        let mut compiled_args = Vec::with_capacity(args.len());
        for arg in args {
            let (v, arg_kind) = self.compile_expr(arg, env)?;
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

        // Restore the correct Kind: Bool-returning functions widen to i64 at
        // their boundary; truncate back to i1 so downstream bool ops work.
        let return_kind = self.fn_return_kinds.get(&callee.0).copied().unwrap_or(Kind::Int);
        if return_kind == Kind::Bool {
            let i1_val = self
                .builder
                .build_int_truncate(
                    result_i64.into_int_value(),
                    self.context.bool_type(),
                    "call_bool",
                )
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            Ok((i1_val.into(), Kind::Bool))
        } else {
            Ok((result_i64, Kind::Int))
        }
    }

    /// Compile `{ e1, e2, … }` in value position into a heap-allocated runtime set.
    ///
    /// All elements must have the same Kind (homogeneous sets only for now).
    /// Returns a pointer-as-i64 with `Kind::Set(elem_kind)`.
    fn compile_set_lit_value(
        &self,
        elements: &[Expr],
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

        let elem_kind = compiled[0].1;
        for &(_, k) in &compiled {
            if k != elem_kind {
                return Err(CompileError::Internal(
                    "mixed element kinds in set literal — \
                     heterogeneous sets not yet supported"
                        .into(),
                ));
            }
        }

        let (set_elem_kind, new_fn, insert_fn) = match elem_kind {
            Kind::Int  => (SetElemKind::Int,  "cantor_set_new_i64",  "cantor_set_insert_i64"),
            Kind::Bool => (SetElemKind::Bool, "cantor_set_new_bool", "cantor_set_insert_bool"),
            Kind::Set(_) => return Err(CompileError::Internal(
                "sets of sets not yet supported".into(),
            )),
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
}
