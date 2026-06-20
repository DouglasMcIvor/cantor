use std::collections::HashMap;

use inkwell::{
    IntPredicate, OptimizationLevel,
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    execution_engine::ExecutionEngine,
    module::Module,
    values::{BasicValueEnum, FunctionValue, IntValue, PointerValue},
};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionBody, FunctionDef, Item, Param, Stmt, UnOp, collect_loop_modified},
    error::CompileError,
    span::{Span, Symbol},
};

/// Return value used to signal assertion failure at runtime.
///
/// `i64::MIN` is used as a sentinel because the sets appearing in Cantor
/// signatures today (Nat, NatPos, NonZeroInt, IntN) exclude i64::MIN.
/// Known limitation: `Int | Fail` functions cannot successfully return the
/// integer -9223372036854775808. A proper tagged-union ABI will fix this later.
pub const FAIL_SENTINEL: i64 = i64::MIN;

/// The LLVM type a Cantor value compiles to. Tracked alongside BasicValueEnum
/// because LLVM erases the distinction between i1 (Bool) and i64 (Int) at
/// the value level, but we need it for correct instruction selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValType {
    Int,  // i64
    Bool, // i1
}

type Env<'ctx> = HashMap<Symbol, (BasicValueEnum<'ctx>, ValType)>;

pub struct Compiler<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    /// The function currently being compiled — needed for appending basic
    /// blocks when lowering `if-then-else` expressions.
    current_fn: Option<FunctionValue<'ctx>>,
    /// The "fail" basic block for the function currently being compiled.
    /// `Some` only when the function is fallible (range contains `Fail`).
    /// Branches here when an `assert` fails at runtime or a `?` propagates.
    fail_bb: Option<BasicBlock<'ctx>>,
}

impl<'ctx> Compiler<'ctx> {
    pub fn new(context: &'ctx Context, name: &str) -> Self {
        Self {
            context,
            module: context.create_module(name),
            builder: context.create_builder(),
            current_fn: None,
            fail_bb: None,
        }
    }

    /// Add a function declaration to the module (no body yet).
    ///
    /// All parameters and the return value are `i64`. Call
    /// [`compile_function_body`] afterwards to fill in the implementation.
    pub fn declare_function(&mut self, name: &str, params: &[Param]) -> FunctionValue<'ctx> {
        let i64_type = self.context.i64_type();
        let param_types: Vec<_> = params.iter().map(|_| i64_type.into()).collect();
        let fn_type = i64_type.fn_type(&param_types, false);
        self.module.add_function(name, fn_type, None)
    }

    /// Compile the body of an already-declared function (expression body).
    ///
    /// Booleans are zero-extended to `i64` so callers always use a uniform
    /// `fn(i64, …) -> i64` signature.
    pub fn compile_function_body(
        &mut self,
        function: FunctionValue<'ctx>,
        params: &[Param],
        body: &Expr,
        is_fallible: bool,
        const_env: &Env<'ctx>,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        self.current_fn = Some(function);

        let entry = self.context.append_basic_block(function, "entry");

        // For fallible functions: create the fail block up front so `?`
        // expressions inside the body can branch to it.
        self.fail_bb = if is_fallible {
            let bb = self.context.append_basic_block(function, "fail");
            self.builder.position_at_end(bb);
            let sentinel = self.context.i64_type().const_int(FAIL_SENTINEL as u64, true);
            self.builder
                .build_return(Some(&sentinel))
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            Some(bb)
        } else {
            None
        };

        self.builder.position_at_end(entry);

        // Seed env with constants, then add parameters (params shadow constants).
        let mut env: Env = const_env.clone();
        for (param, llvm_param) in params.iter().zip(function.get_param_iter()) {
            llvm_param.set_name(&param.name.0);
            env.insert(param.name.clone(), (llvm_param, ValType::Int));
        }

        let (val, ty) = self.compile_expr(body, &env)?;

        let i64_type = self.context.i64_type();
        let ret_val = if ty == ValType::Bool {
            self.builder
                .build_int_z_extend(val.into_int_value(), i64_type, "bool_to_i64")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into()
        } else {
            val
        };

        self.builder
            .build_return(Some(&ret_val))
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        Ok(function)
    }

    /// Compile the body of an already-declared function (block body).
    pub fn compile_block_body(
        &mut self,
        function: FunctionValue<'ctx>,
        params: &[Param],
        stmts: &[Stmt],
        is_fallible: bool,
        const_env: &Env<'ctx>,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        self.current_fn = Some(function);

        let entry = self.context.append_basic_block(function, "entry");

        self.fail_bb = if is_fallible {
            let bb = self.context.append_basic_block(function, "fail");
            self.builder.position_at_end(bb);
            let sentinel = self.context.i64_type().const_int(FAIL_SENTINEL as u64, true);
            self.builder
                .build_return(Some(&sentinel))
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            Some(bb)
        } else {
            None
        };

        self.builder.position_at_end(entry);

        // Seed env with constants, then add parameters (params shadow constants).
        let mut env: Env = const_env.clone();
        for (param, llvm_param) in params.iter().zip(function.get_param_iter()) {
            llvm_param.set_name(&param.name.0);
            env.insert(param.name.clone(), (llvm_param, ValType::Int));
        }

        let return_val = self.compile_stmts(stmts, &mut env, &HashMap::new())?;

        let i64_type = self.context.i64_type();
        let ret_val = match return_val {
            Some((val, ValType::Bool)) => self
                .builder
                .build_int_z_extend(val.into_int_value(), i64_type, "bool_to_i64")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into(),
            Some((val, ValType::Int)) => val,
            None => {
                return Err(CompileError::Internal(
                    "block body has no return expression".into(),
                ))
            }
        };

        self.builder
            .build_return(Some(&ret_val))
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        Ok(function)
    }

    /// Declare and compile a function in one step (expression body, infallible).
    ///
    /// Convenience wrapper used by tests.
    pub fn compile_function(
        &mut self,
        name: &str,
        params: &[Param],
        body: &Expr,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        let function = self.declare_function(name, params);
        self.compile_function_body(function, params, body, false, &Env::new())
    }

    /// Process a sequence of statements, returning the last expression value.
    ///
    /// `alloca_map` is non-empty when compiling a loop body: it maps each
    /// loop-modified variable to its alloca pointer so assignments also write
    /// through to the alloca (making the updated value visible to the loop
    /// header on the next iteration).
    fn compile_stmts(
        &mut self,
        stmts: &[Stmt],
        env: &mut Env<'ctx>,
        alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<Option<(BasicValueEnum<'ctx>, ValType)>, CompileError> {
        let mut last = None;
        for stmt in stmts {
            last = None;
            match stmt {
                Stmt::MutLet { name, value, .. } | Stmt::Assign { name, value, .. } => {
                    let result = self.compile_expr(value, env)?;
                    // If this variable is backed by an alloca (i.e. we're in a loop
                    // body and this variable persists across iterations), write
                    // through so the loop header sees the updated value.
                    if let Some(&ptr) = alloca_map.get(name) {
                        let i64_type = self.context.i64_type();
                        let val_i64: IntValue<'ctx> = if result.1 == ValType::Bool {
                            self.builder
                                .build_int_z_extend(result.0.into_int_value(), i64_type, "bool_ext")
                                .map_err(|e| CompileError::Internal(e.to_string()))?
                        } else {
                            result.0.into_int_value()
                        };
                        self.builder
                            .build_store(ptr, val_i64)
                            .map_err(|e| CompileError::Internal(e.to_string()))?;
                    }
                    env.insert(name.clone(), result);
                }

                // Static-only constructs — no runtime representation.
                Stmt::Require { .. } | Stmt::Assume { .. } => {}

                Stmt::Assert { predicate, .. } => {
                    self.compile_assert(predicate, env)?;
                }

                Stmt::Expr(e) => {
                    last = Some(self.compile_expr(e, env)?);
                }

                Stmt::Block(inner) => {
                    last = self.compile_stmts(inner, env, alloca_map)?;
                }

                Stmt::While { cond, body, .. } => {
                    self.compile_while(cond, body, env, alloca_map)?;
                }

                Stmt::ForIn { var, set, body, .. } => {
                    self.compile_for_in(var, set, body, env, alloca_map)?;
                }
            }
        }
        Ok(last)
    }

    /// Emit LLVM IR for `while cond { body }`.
    ///
    /// Variables assigned inside `body` that already exist in `env` are
    /// given alloca-backed storage so their values persist across iterations.
    /// New allocas are merged with any inherited from an outer loop so nested
    /// loops correctly write through to the outermost alloca.
    fn compile_while(
        &mut self,
        cond: &Expr,
        body: &[Stmt],
        env: &mut Env<'ctx>,
        outer_alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<(), CompileError> {
        let i64_type = self.context.i64_type();

        // Build the alloca map for this loop: start from the outer map (so
        // nested loops reuse the same allocas for shared variables) and add
        // new allocas for any body-modified variable not already covered.
        let modified = collect_loop_modified(body);
        let mut inner_alloca_map: HashMap<Symbol, PointerValue<'ctx>> = outer_alloca_map.clone();

        for name in &modified {
            if inner_alloca_map.contains_key(name) {
                continue; // already backed by an outer-loop alloca
            }
            if let Some(&(val, ty)) = env.get(name) {
                let ptr = self.builder
                    .build_alloca(i64_type, &name.0)
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                let val_i64: IntValue<'ctx> = if ty == ValType::Bool {
                    self.builder
                        .build_int_z_extend(val.into_int_value(), i64_type, "bool_ext")
                        .map_err(|e| CompileError::Internal(e.to_string()))?
                } else {
                    val.into_int_value()
                };
                self.builder
                    .build_store(ptr, val_i64)
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                inner_alloca_map.insert(name.clone(), ptr);
            }
        }

        let function = self.current_fn.ok_or_else(|| {
            CompileError::Internal("while loop outside a function".into())
        })?;

        let cond_bb  = self.context.append_basic_block(function, "while_cond");
        let body_bb  = self.context.append_basic_block(function, "while_body");
        let after_bb = self.context.append_basic_block(function, "while_after");

        self.builder.build_unconditional_branch(cond_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // ── Condition block ────────────────────────────────────────────────
        // Reload alloca'd variables so the condition sees the latest values.
        self.builder.position_at_end(cond_bb);
        let mut loop_env = env.clone();
        for (name, &ptr) in &inner_alloca_map {
            let val = self.builder
                .build_load(i64_type, ptr, &name.0)
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            loop_env.insert(name.clone(), (val.into(), ValType::Int));
        }
        let (cond_val, _) = self.compile_expr(cond, &loop_env)?;
        self.builder
            .build_conditional_branch(cond_val.into_int_value(), body_bb, after_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // ── Body block ─────────────────────────────────────────────────────
        self.builder.position_at_end(body_bb);
        let mut body_env = loop_env;
        self.compile_stmts(body, &mut body_env, &inner_alloca_map)?;
        self.builder.build_unconditional_branch(cond_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // ── After block ────────────────────────────────────────────────────
        // Reload the final alloca values back into the caller's env so
        // subsequent statements in the enclosing block see the results.
        self.builder.position_at_end(after_bb);
        for (name, &ptr) in &inner_alloca_map {
            let val = self.builder
                .build_load(i64_type, ptr, &format!("{}_final", name.0))
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            env.insert(name.clone(), (val.into(), ValType::Int));
        }

        Ok(())
    }

    /// Emit LLVM IR for `for x in S { body }`.
    ///
    /// Only set literals `{e1, e2, …}` are supported as iterables for now —
    /// named/generative sets need a runtime set representation that doesn't
    /// exist yet.  The body is unrolled: compiled once per element in source
    /// order, with `var` bound to the element value each time.  Values of
    /// outer-loop alloca-backed variables propagate correctly because
    /// `compile_stmts` writes through to the alloca on every assignment.
    fn compile_for_in(
        &mut self,
        var: &Symbol,
        set: &Expr,
        body: &[Stmt],
        env: &mut Env<'ctx>,
        alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<(), CompileError> {
        let ExprKind::SetLit(elements) = &set.kind else {
            return Err(CompileError::Internal(
                "for loop: only set literals `{e1, e2, ...}` are supported as iterables \
                 in this version (named/generative sets need a runtime set representation)"
                    .into(),
            ));
        };
        let i64_type = self.context.i64_type();
        for elem in elements {
            let (elem_val, elem_ty) = self.compile_expr(elem, env)?;
            let val_i64: BasicValueEnum = if elem_ty == ValType::Bool {
                self.builder
                    .build_int_z_extend(elem_val.into_int_value(), i64_type, "bool_ext")
                    .map_err(|e| CompileError::Internal(e.to_string()))?
                    .into()
            } else {
                elem_val
            };
            env.insert(var.clone(), (val_i64, ValType::Int));
            self.compile_stmts(body, env, alloca_map)?;
        }
        Ok(())
    }

    /// Emit a runtime check for `assert predicate`.
    ///
    /// If the function is fallible, branches to `fail_bb` when the predicate
    /// is false.  In an infallible function, the checker either proved the
    /// assertion or returned Unknown; we skip the check (no runtime overhead).
    fn compile_assert(
        &mut self,
        predicate: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let Some(fail_bb) = self.fail_bb else {
            return Ok(());
        };

        let function = self.current_fn.ok_or_else(|| {
            CompileError::Internal("assert outside a function".into())
        })?;

        let (cond_val, _) = self.compile_expr(predicate, env)?;
        let cond_i1 = cond_val.into_int_value();

        let pass_bb = self.context.append_basic_block(function, "assert_pass");
        self.builder
            .build_conditional_branch(cond_i1, pass_bb, fail_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        self.builder.position_at_end(pass_bb);
        Ok(())
    }

    /// Emit LLVM IR for an expression, returning the value and its Cantor type.
    pub(crate) fn compile_expr(
        &self,
        expr: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, ValType), CompileError> {
        match &expr.kind {
            ExprKind::IntLit(n) => {
                let v = self.context.i64_type().const_int(*n as u64, true);
                Ok((v.into(), ValType::Int))
            }
            ExprKind::BoolLit(b) => {
                let v = self.context.bool_type().const_int(*b as u64, false);
                Ok((v.into(), ValType::Bool))
            }
            ExprKind::Var(sym) => env
                .get(sym)
                .map(|&(v, t)| (v, t))
                .ok_or_else(|| CompileError::UndefinedVariable {
                    name: sym.0.clone(),
                    span: expr.span,
                }),
            ExprKind::UnOp { op, expr: inner } => {
                self.compile_unop(*op, inner, env, expr.span)
            }
            ExprKind::BinOp { op, lhs, rhs } => {
                self.compile_binop(*op, lhs, rhs, env, expr.span)
            }
            ExprKind::Call { callee, args } => {
                self.compile_call(callee, args, env, expr.span)
            }
            ExprKind::If { cond, then_expr, else_expr } => {
                self.compile_if(cond, then_expr, else_expr, env)
            }
            ExprKind::SetLit(_) => Err(CompileError::Internal(
                "set literals are only valid in signature position, not as values".into(),
            )),
            ExprKind::Try(inner) => self.compile_try(inner, env),
        }
    }

    /// Compile `expr?` — propagate `Fail` from a fallible call.
    ///
    /// Calls the inner expression, checks whether the result equals
    /// `FAIL_SENTINEL`, and branches to `fail_bb` if so.
    fn compile_try(
        &self,
        inner: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, ValType), CompileError> {
        let (val, _) = self.compile_expr(inner, env)?;
        let result_i64 = val.into_int_value();

        let Some(fail_bb) = self.fail_bb else {
            return Err(CompileError::Internal(
                "`?` used in an infallible function (add `| Fail` to the range)".into(),
            ));
        };

        let function = self.current_fn.ok_or_else(|| {
            CompileError::Internal("`?` outside a function".into())
        })?;

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
        Ok((result_i64.into(), ValType::Int))
    }

    fn compile_if(
        &self,
        cond: &Expr,
        then_expr: &Expr,
        else_expr: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, ValType), CompileError> {
        let function = self.current_fn.ok_or_else(|| {
            CompileError::Internal("if-then-else outside a function".into())
        })?;

        let (cond_val, _) = self.compile_expr(cond, env)?;
        let cond_i1 = cond_val.into_int_value();

        let then_bb  = self.context.append_basic_block(function, "then");
        let else_bb  = self.context.append_basic_block(function, "else");
        let merge_bb = self.context.append_basic_block(function, "merge");

        self.builder
            .build_conditional_branch(cond_i1, then_bb, else_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // Then branch
        self.builder.position_at_end(then_bb);
        let (then_val, then_ty) = self.compile_expr(then_expr, env)?;
        self.builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let then_bb_end = self.builder.get_insert_block().unwrap();

        // Else branch
        self.builder.position_at_end(else_bb);
        let (else_val, _else_ty) = self.compile_expr(else_expr, env)?;
        self.builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let else_bb_end = self.builder.get_insert_block().unwrap();

        // Merge with phi
        self.builder.position_at_end(merge_bb);
        let phi = self.builder
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
    ) -> Result<(BasicValueEnum<'ctx>, ValType), CompileError> {
        let (val, _ty) = self.compile_expr(inner, env)?;
        let iv = val.into_int_value();
        match op {
            UnOp::Neg => {
                let v = self
                    .builder
                    .build_int_neg(iv, "neg")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), ValType::Int))
            }
            // build_not is bitwise NOT; on i1 this is logical NOT (0↔1).
            UnOp::Not => {
                let v = self
                    .builder
                    .build_not(iv, "not")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), ValType::Bool))
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
    ) -> Result<(BasicValueEnum<'ctx>, ValType), CompileError> {
        // Membership checks: only the LHS is a value; the RHS is a set expression.
        match op {
            BinOp::In => {
                let (lv, _) = self.compile_expr(lhs, env)?;
                let pred = self.compile_membership(lv.into_int_value(), rhs)?;
                return Ok((pred.into(), ValType::Bool));
            }
            BinOp::NotIn => {
                let (lv, _) = self.compile_expr(lhs, env)?;
                let pred = self.compile_membership(lv.into_int_value(), rhs)?;
                let neg = self.builder.build_not(pred, "not_in")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                return Ok((neg.into(), ValType::Bool));
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
                Ok((v.into(), ValType::Int))
            }};
        }
        macro_rules! cmp_op {
            ($pred:ident, $name:literal) => {{
                let v = b
                    .build_int_compare(IntPredicate::$pred, li, ri, $name)
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), ValType::Bool))
            }};
        }
        macro_rules! bool_op {
            ($method:ident, $name:literal) => {{
                let v = b
                    .$method(li, ri, $name)
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                Ok((v.into(), ValType::Bool))
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

    /// Compile `val ∈ set_expr` to an `i1` LLVM predicate.
    ///
    /// Mirrors `membership_constraint` in the solver but emits LLVM IR instead
    /// of cvc5 terms.  The same named sets are supported: Int, Nat, NatPos,
    /// NonZeroInt, Int8/16/32/64, set literals, and set union/difference/intersection.
    fn compile_membership(
        &self,
        val: IntValue<'ctx>,
        set_expr: &Expr,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let b = &self.builder;
        let i64 = self.context.i64_type();
        let bool = self.context.bool_type();

        match &set_expr.kind {
            ExprKind::Var(sym) => match sym.0.as_str() {
                "Int" => Ok(bool.const_int(1, false)),
                "Nat" => b
                    .build_int_compare(IntPredicate::SGE, val, i64.const_int(0, true), "in_nat")
                    .map_err(|e| CompileError::Internal(e.to_string())),
                "NatPos" => b
                    .build_int_compare(IntPredicate::SGT, val, i64.const_int(0, true), "in_natpos")
                    .map_err(|e| CompileError::Internal(e.to_string())),
                "NonZeroInt" => b
                    .build_int_compare(IntPredicate::NE, val, i64.const_int(0, true), "in_nonzero")
                    .map_err(|e| CompileError::Internal(e.to_string())),
                "Fail" => Ok(bool.const_int(0, false)),
                "Int8"  => self.compile_bounded_membership(val, i8::MIN  as i64, i8::MAX  as i64),
                "Int16" => self.compile_bounded_membership(val, i16::MIN as i64, i16::MAX as i64),
                "Int32" => self.compile_bounded_membership(val, i32::MIN as i64, i32::MAX as i64),
                "Int64" => self.compile_bounded_membership(val, i64::MIN,        i64::MAX        ),
                other   => Err(CompileError::Internal(format!("unknown set `{other}`"))),
            },

            ExprKind::SetLit(elements) => {
                if elements.is_empty() {
                    return Ok(bool.const_int(0, false));
                }
                let mut acc: Option<IntValue<'ctx>> = None;
                for elem in elements {
                    let ExprKind::IntLit(n) = &elem.kind else {
                        return Err(CompileError::Internal("non-literal in set literal".into()));
                    };
                    let elem_val = i64.const_int(*n as u64, true);
                    let eq = b.build_int_compare(IntPredicate::EQ, val, elem_val, "set_eq")
                        .map_err(|e| CompileError::Internal(e.to_string()))?;
                    acc = Some(match acc {
                        None => eq,
                        Some(prev) => b.build_or(prev, eq, "set_or")
                            .map_err(|e| CompileError::Internal(e.to_string()))?,
                    });
                }
                Ok(acc.unwrap())
            }

            // t ∈ A - B  →  (t ∈ A) && !(t ∈ B)
            ExprKind::BinOp { op: BinOp::Sub, lhs, rhs } => {
                let in_a   = self.compile_membership(val, lhs)?;
                let in_b   = self.compile_membership(val, rhs)?;
                let not_b  = b.build_not(in_b, "not_b").map_err(|e| CompileError::Internal(e.to_string()))?;
                b.build_and(in_a, not_b, "set_diff").map_err(|e| CompileError::Internal(e.to_string()))
            }

            // t ∈ A | B  →  (t ∈ A) || (t ∈ B)
            ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                b.build_or(in_a, in_b, "set_union").map_err(|e| CompileError::Internal(e.to_string()))
            }

            // t ∈ A & B  →  (t ∈ A) && (t ∈ B)
            ExprKind::BinOp { op: BinOp::Intersect, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                b.build_and(in_a, in_b, "set_inter").map_err(|e| CompileError::Internal(e.to_string()))
            }

            _ => Err(CompileError::Internal("unsupported set expression in membership check".into())),
        }
    }

    fn compile_bounded_membership(
        &self,
        val: IntValue<'ctx>,
        min: i64,
        max: i64,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let b  = &self.builder;
        let i64 = self.context.i64_type();
        let lo  = i64.const_int(min as u64, true);
        let hi  = i64.const_int(max as u64, true);
        let ge  = b.build_int_compare(IntPredicate::SGE, val, lo, "ge")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let le  = b.build_int_compare(IntPredicate::SLE, val, hi, "le")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        b.build_and(ge, le, "bounded").map_err(|e| CompileError::Internal(e.to_string()))
    }

    fn compile_call(
        &self,
        callee: &Symbol,
        args: &[Expr],
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, ValType), CompileError> {
        let function = self.module.get_function(&callee.0).ok_or_else(|| {
            CompileError::UndefinedVariable { name: callee.0.clone(), span }
        })?;

        let mut compiled_args = Vec::with_capacity(args.len());
        for arg in args {
            let (v, _) = self.compile_expr(arg, env)?;
            compiled_args.push(v.into());
        }

        let call = self
            .builder
            .build_call(function, &compiled_args, "call")
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        let result = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("void return in expression position".into()))?;

        Ok((result, ValType::Int))
    }

    /// Consume the compiler and hand the module to a JIT engine.
    pub fn into_jit_engine(self) -> Result<ExecutionEngine<'ctx>, String> {
        self.module
            .create_jit_execution_engine(OptimizationLevel::None)
            .map_err(|e| e.to_string())
    }

    pub fn print_ir(&self) {
        self.module.print_to_stderr();
    }
}

/// True if any `|`-union branch of the range expression is the `Fail` set.
pub fn range_contains_fail(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::Var(sym) => sym.0 == "Fail",
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            range_contains_fail(lhs) || range_contains_fail(rhs)
        }
        _ => false,
    }
}

/// Compile every function in `items` into a single JIT module.
///
/// Two-pass: all functions are declared first so that forward and mutual
/// calls resolve, then bodies are compiled in order.
/// Evaluate a constant expression at compile time.
///
/// Only integer arithmetic and references to already-evaluated constants are
/// supported. This is intentionally simple — constants are auto-constexpr and
/// the compiler inlines the result everywhere.
fn eval_const(expr: &Expr, known: &HashMap<Symbol, i64>) -> Result<i64, CompileError> {
    match &expr.kind {
        ExprKind::IntLit(n) => Ok(*n),
        ExprKind::Var(sym) => known.get(sym).copied().ok_or_else(|| {
            CompileError::Internal(format!(
                "constant `{}` is undefined or not yet evaluated (constants must appear before use in file order)",
                sym.0
            ))
        }),
        ExprKind::UnOp { op: UnOp::Neg, expr: inner } => Ok(-eval_const(inner, known)?),
        ExprKind::BinOp { op, lhs, rhs } => {
            let l = eval_const(lhs, known)?;
            let r = eval_const(rhs, known)?;
            match op {
                BinOp::Add => Ok(l.wrapping_add(r)),
                BinOp::Sub => Ok(l.wrapping_sub(r)),
                BinOp::Mul => Ok(l.wrapping_mul(r)),
                BinOp::Div => {
                    if r == 0 {
                        Err(CompileError::Internal("division by zero in constant expression".into()))
                    } else {
                        Ok(l / r)
                    }
                }
                _ => Err(CompileError::Internal(
                    "only integer arithmetic is supported in constant expressions".into(),
                )),
            }
        }
        _ => Err(CompileError::Internal(
            "only integer arithmetic is supported in constant expressions".into(),
        )),
    }
}

pub fn compile_file<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
) -> Result<ExecutionEngine<'ctx>, CompileError> {
    let mut compiler = Compiler::new(ctx, "cantor");

    // Pass 0 — evaluate constants and build a shared env of inlined values.
    let mut const_vals: HashMap<Symbol, i64> = HashMap::new();
    for item in items {
        if let Item::ConstDef(def) = item {
            let val = eval_const(&def.value, &const_vals)?;
            const_vals.insert(def.name.clone(), val);
        }
    }
    let i64_type = ctx.i64_type();
    let const_env: Env<'ctx> = const_vals
        .iter()
        .map(|(sym, &val)| {
            let llvm_val = i64_type.const_int(val as u64, true);
            (sym.clone(), (llvm_val.into(), ValType::Int))
        })
        .collect();

    // Pass 1 — declare all function signatures so forward calls resolve.
    let decls: Vec<(FunctionValue<'ctx>, &FunctionDef)> = items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => {
                let fn_val = compiler.declare_function(&def.name.0, &def.params);
                Some((fn_val, def))
            }
            Item::ConstDef(_) => None,
        })
        .collect();

    // Pass 2 — compile bodies with constants available.
    for (fn_val, def) in decls {
        let is_fallible = def.sigs.iter().any(|s| range_contains_fail(&s.range));
        match &def.body {
            FunctionBody::Expr(e) => {
                compiler.compile_function_body(fn_val, &def.params, e, is_fallible, &const_env)?;
            }
            FunctionBody::Block(stmts) => {
                compiler.compile_block_body(fn_val, &def.params, stmts, is_fallible, &const_env)?;
            }
        }
    }

    compiler
        .into_jit_engine()
        .map_err(|e| CompileError::Internal(e))
}
