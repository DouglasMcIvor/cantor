use std::collections::HashMap;

use inkwell::{
    IntPredicate, OptimizationLevel,
    builder::Builder,
    context::Context,
    execution_engine::ExecutionEngine,
    module::Module,
    values::{BasicValueEnum, FunctionValue},
};

use crate::{
    ast::{BinOp, Expr, ExprKind, Param, UnOp},
    error::CompileError,
    span::{Span, Symbol},
};

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
}

impl<'ctx> Compiler<'ctx> {
    pub fn new(context: &'ctx Context, name: &str) -> Self {
        Self {
            context,
            module: context.create_module(name),
            builder: context.create_builder(),
            current_fn: None,
        }
    }

    /// Compile a named function. All parameters are `i64` for now; the return
    /// value is always `i64` (booleans are zero-extended so the JIT harness
    /// can use a uniform `fn() -> i64` signature).
    pub fn compile_function(
        &mut self,
        name: &str,
        params: &[Param],
        body: &Expr,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        let i64_type = self.context.i64_type();
        let param_types: Vec<_> = params.iter().map(|_| i64_type.into()).collect();
        let fn_type = i64_type.fn_type(&param_types, false);
        let function = self.module.add_function(name, fn_type, None);
        self.current_fn = Some(function);

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let mut env: Env = HashMap::new();
        for (param, llvm_param) in params.iter().zip(function.get_param_iter()) {
            llvm_param.set_name(&param.name.0);
            env.insert(param.name.clone(), (llvm_param, ValType::Int));
        }

        let (val, ty) = self.compile_expr(body, &env)?;

        // Bool results are zero-extended to i64 so callers always see i64.
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
        }
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
            BinOp::In | BinOp::NotIn
            | BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
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
