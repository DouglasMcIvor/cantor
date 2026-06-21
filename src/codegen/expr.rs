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

use super::{Compiler, Env, FAIL_SENTINEL};

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
        }
    }

    fn compile_try(
        &self,
        inner: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (val, _) = self.compile_expr(inner, env)?;
        let result_i64 = val.into_int_value();

        let Some(fail_bb) = self.fail_bb else {
            return Err(CompileError::Internal(
                "`?` used in an infallible function (add `| Fail` to the range)".into(),
            ));
        };

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::Internal("`?` outside a function".into()))?;

        let sentinel = self.context.i64_type().const_int(FAIL_SENTINEL as u64, true);
        let is_fail = self
            .builder
            .build_int_compare(IntPredicate::EQ, result_i64, sentinel, "is_fail")
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        let ok_bb = self.context.append_basic_block(function, "try_ok");
        self.builder
            .build_conditional_branch(is_fail, fail_bb, ok_bb)
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
        match op {
            BinOp::In => {
                let (lv, _) = self.compile_expr(lhs, env)?;
                let pred = self.compile_membership(lv.into_int_value(), rhs)?;
                return Ok((pred.into(), Kind::Bool));
            }
            BinOp::NotIn => {
                let (lv, _) = self.compile_expr(lhs, env)?;
                let pred = self.compile_membership(lv.into_int_value(), rhs)?;
                let neg = self
                    .builder
                    .build_not(pred, "not_in")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                return Ok((neg.into(), Kind::Bool));
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
            BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
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
