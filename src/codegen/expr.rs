use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{
    ast::{BinOp, Expr, ExprKind, UnOp},
    error::CompileError,
    kind::{Kind, SetElemKind},
    span::{Span, Symbol},
};

// Names of the builder/finish functions keyed by vector element kind.
fn vec_builder_fns(ek: &Kind) -> Result<(&'static str, &'static str, &'static str, &'static str), String> {
    match ek {
        Kind::Int  => Ok(("cantor_vec_builder_new_i64",  "cantor_vec_builder_push_i64",
                          "cantor_vec_builder_finish_i64", "cantor_vec_len_i64")),
        Kind::Bool => Ok(("cantor_vec_builder_new_bool", "cantor_vec_builder_push_bool",
                          "cantor_vec_builder_finish_bool", "cantor_vec_len_bool")),
        other => Err(format!("vec_builder_fns: unsupported element kind {other:?}")),
    }
}

use super::{Compiler, Env};


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
                .map(|(v, t)| (*v, t.clone()))
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
                // fail → {i1=1, i64=0}
                let zero = self.context.i64_type().const_int(0, false);
                let v = self.build_fail_struct(zero.into())?;
                Ok((v, Kind::Tuple(vec![Kind::Fail, Kind::Int])))
            }
            ExprKind::FailWith(inner) => {
                // fail n → {i1=1, i64=n}
                let (v, _) = self.compile_expr(inner, env)?;
                let s = self.build_fail_struct(v)?;
                Ok((s, Kind::Tuple(vec![Kind::Fail, Kind::Int])))
            }
            ExprKind::Tuple(elems) => self.compile_tuple(elems, env),
            ExprKind::Proj { base, index } => self.compile_proj(base, *index, env),
            ExprKind::KleeneStar(_) => Err(CompileError::Internal(
                "X* is a set expression and cannot appear in value position".into(),
            )),
        }
    }

    fn compile_try(
        &self,
        inner: &Expr,
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
        let (then_val_raw, then_ty) = self.compile_expr(then_expr, env)?;
        let then_bb_cur = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(else_bb);
        let (else_val_raw, else_ty) = self.compile_expr(else_expr, env)?;
        let else_bb_cur = self.builder.get_insert_block().unwrap();

        // When one branch is a fail struct and the other is not, coerce the
        // non-struct branch to {i1=0, i64=val} before the phi merge.
        let is_fail_struct = |k: &Kind| matches!(k, Kind::Tuple(e) if e.first() == Some(&Kind::Fail));
        let needs_coerce = is_fail_struct(&then_ty) || is_fail_struct(&else_ty);

        // Detect cross-kind branches that need a tagged-union wrapper.
        // Handles `then : Kind::Tuple` vs `else : Kind::Int` (and vice versa).
        let needs_tagged_union = !needs_coerce
            && then_ty != else_ty
            && (matches!(&then_ty, Kind::Tuple(_)) || matches!(&else_ty, Kind::Tuple(_)))
            && !matches!(&then_ty, Kind::TaggedUnion(_))
            && !matches!(&else_ty, Kind::TaggedUnion(_));

        // Detect the case where one or both branches are already a TaggedUnion and
        // the kinds differ.  Covers both the simple append (one branch is a plain kind)
        // and the full merge (both branches are different TaggedUnions).
        let needs_extend_tagged_union = !needs_coerce
            && !needs_tagged_union
            && then_ty != else_ty
            && (matches!(&then_ty, Kind::TaggedUnion(_)) || matches!(&else_ty, Kind::TaggedUnion(_)));

        let (then_val, else_val, result_ty) = if needs_coerce {
            self.builder.position_at_end(then_bb_cur);
            let tv = self.coerce_to_fail_struct(then_val_raw, &then_ty)?;
            self.builder.position_at_end(else_bb_cur);
            let ev = self.coerce_to_fail_struct(else_val_raw, &else_ty)?;
            (tv, ev, Kind::Tuple(vec![Kind::Fail, Kind::Int]))
        } else if needs_tagged_union {
            let arms = vec![then_ty.clone(), else_ty.clone()];
            self.builder.position_at_end(then_bb_cur);
            let tv = self.build_tagged_union_value(0, then_val_raw, &then_ty, &arms)?;
            self.builder.position_at_end(else_bb_cur);
            let ev = self.build_tagged_union_value(1, else_val_raw, &else_ty, &arms)?;
            (tv, ev, Kind::TaggedUnion(arms))
        } else if needs_extend_tagged_union {
            match (&then_ty, &else_ty) {
                (Kind::TaggedUnion(then_inner), Kind::TaggedUnion(else_inner)) => {
                    // Both branches are different TaggedUnions.
                    // Merge: start with then_inner, append unique arms from else_inner.
                    let mut merged_arms = then_inner.clone();
                    for arm in else_inner {
                        if !merged_arms.contains(arm) {
                            merged_arms.push(arm.clone());
                        }
                    }
                    // Mapping: else_arm_idx → merged_arm_idx (for runtime re-tagging).
                    let else_to_merged: Vec<usize> = else_inner.iter()
                        .map(|arm| merged_arms.iter().position(|m| m == arm).unwrap())
                        .collect();

                    self.builder.position_at_end(then_bb_cur);
                    let tv = self.rewrap_tagged_union_value(then_val_raw, then_inner, &merged_arms)?;

                    self.builder.position_at_end(else_bb_cur);
                    let old_struct = AggregateValueEnum::StructValue(else_val_raw.into_struct_value());
                    let old_tag = self.builder
                        .build_extract_value(old_struct, 0, "tu_merge_tag")
                        .map_err(|e| CompileError::Internal(e.to_string()))?
                        .into_int_value();
                    let new_tag = self.remap_tagged_union_tag(old_tag, &else_to_merged)?;
                    let ev = self.rewrap_tagged_union_with_tag(else_val_raw, else_inner, &merged_arms, new_tag)?;

                    (tv, ev, Kind::TaggedUnion(merged_arms))
                }
                (Kind::TaggedUnion(inner_arms), _) => {
                    // then = TaggedUnion, else = plain kind: append else as new arm.
                    let n = inner_arms.len();
                    let mut new_arms = inner_arms.clone();
                    new_arms.push(else_ty.clone());
                    self.builder.position_at_end(then_bb_cur);
                    let tv = self.rewrap_tagged_union_value(then_val_raw, inner_arms, &new_arms)?;
                    self.builder.position_at_end(else_bb_cur);
                    let ev = self.build_tagged_union_value(n, else_val_raw, &else_ty, &new_arms)?;
                    (tv, ev, Kind::TaggedUnion(new_arms))
                }
                (_, Kind::TaggedUnion(inner_arms)) => {
                    // then = plain kind, else = TaggedUnion: append then as new arm.
                    let n = inner_arms.len();
                    let mut new_arms = inner_arms.clone();
                    new_arms.push(then_ty.clone());
                    self.builder.position_at_end(then_bb_cur);
                    let tv = self.build_tagged_union_value(n, then_val_raw, &then_ty, &new_arms)?;
                    self.builder.position_at_end(else_bb_cur);
                    let ev = self.rewrap_tagged_union_value(else_val_raw, inner_arms, &new_arms)?;
                    (tv, ev, Kind::TaggedUnion(new_arms))
                }
                _ => unreachable!("needs_extend_tagged_union guarantees at least one TaggedUnion branch"),
            }
        } else {
            (then_val_raw, else_val_raw, then_ty)
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
                let pred = if let Kind::TaggedUnion(ref arms) = lk {
                    // Tagged-union values: check the tag against the matching arm.
                    self.compile_tagged_union_membership(lv, arms, rhs)?
                } else if let ExprKind::Var(sym) = &rhs.kind {
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
            let len_fn = match &kind {
                Kind::Vector(ek) => match ek.as_ref() {
                    Kind::Int  => "cantor_vec_len_i64",
                    Kind::Bool => "cantor_vec_len_bool",
                    other => return Err(CompileError::Internal(format!(
                        "len() on Vector({other:?}) not yet supported"
                    ))),
                },
                _ => return Err(CompileError::Internal(
                    "len() requires a vector (X*) argument".into(),
                )),
            };
            let fn_val = self.module.get_function(len_fn)
                .ok_or_else(|| CompileError::Internal(format!("{len_fn} not declared")))?;
            let result = self.builder
                .build_call(fn_val, &[ptr.into()], "len")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::Internal("len fn returned void".into()))?;
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
            Kind::Tuple(_) | Kind::Union(_) | Kind::TaggedUnion(_) => Ok((result_i64, return_kind)),
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
            Kind::Fail | Kind::Tuple(_) | Kind::Union(_) | Kind::TaggedUnion(_) => return Err(CompileError::Internal(
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
        elems: &[Expr],
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

    /// Build an Arrow vector from a Tuple value at a function return boundary.
    ///
    /// Called when the function's declared range is `Kind::Vector(elem_kind)` but
    /// the body compiled to `Kind::Tuple(elems)` — the typical case for an array
    /// literal `[1, 2, 3]` in an `X*` range.  Emits:
    ///   builder = cantor_vec_builder_new_<ek>()
    ///   cantor_vec_builder_push_<ek>(builder, elem_0)
    ///   ...
    ///   vec_ptr = cantor_vec_builder_finish_<ek>(builder)
    pub(crate) fn compile_tuple_as_vector(
        &self,
        tuple_val: inkwell::values::BasicValueEnum<'ctx>,
        tuple_elems: &[Kind],
        elem_kind: &Kind,
    ) -> Result<(inkwell::values::BasicValueEnum<'ctx>, Kind), CompileError> {
        let (new_fn, push_fn, finish_fn, _) = vec_builder_fns(elem_kind)
            .map_err(CompileError::Internal)?;
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());

        let new_fn_val = self.module.get_function(new_fn)
            .ok_or_else(|| CompileError::Internal(format!("{new_fn} not declared")))?;
        let push_fn_val = self.module.get_function(push_fn)
            .ok_or_else(|| CompileError::Internal(format!("{push_fn} not declared")))?;
        let finish_fn_val = self.module.get_function(finish_fn)
            .ok_or_else(|| CompileError::Internal(format!("{finish_fn} not declared")))?;

        let builder_ptr = self.builder
            .build_call(new_fn_val, &[], "vec_builder")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("vec builder new returned void".into()))?;

        let sv = inkwell::values::AggregateValueEnum::StructValue(tuple_val.into_struct_value());
        let i64t = self.context.i64_type();
        for (i, ek) in tuple_elems.iter().enumerate() {
            let elem = self.builder
                .build_extract_value(sv, i as u32, "vec_elem")
                .map_err(err)?;
            let elem_i64 = if *ek == Kind::Bool {
                self.builder
                    .build_int_z_extend(elem.into_int_value(), i64t, "vec_elem_ext")
                    .map_err(err)?
                    .into()
            } else {
                elem
            };
            self.builder
                .build_call(push_fn_val, &[builder_ptr.into(), elem_i64.into()], "vec_push")
                .map_err(err)?;
        }

        let vec_ptr = self.builder
            .build_call(finish_fn_val, &[builder_ptr.into()], "vec_ptr")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("vec builder finish returned void".into()))?;

        Ok((vec_ptr, Kind::Vector(Box::new(elem_kind.clone()))))
    }

    /// Compile `base.N` — extract element N from a tuple.
    fn compile_proj(
        &self,
        base: &Expr,
        index: usize,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (base_val, base_kind) = self.compile_expr(base, env)?;
        let elem_kinds = match base_kind {
            Kind::Tuple(ek) => ek,
            _ => return Err(CompileError::Internal(
                "projection `.N` applied to non-tuple value".into(),
            )),
        };
        if index >= elem_kinds.len() {
            return Err(CompileError::Internal(format!(
                "tuple index {index} out of bounds (tuple has {} elements)",
                elem_kinds.len()
            )));
        }
        let elem_val = self.builder
            .build_extract_value(
                AggregateValueEnum::StructValue(base_val.into_struct_value()),
                index as u32,
                "proj",
            )
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        Ok((elem_val, elem_kinds[index].clone()))
    }
}
