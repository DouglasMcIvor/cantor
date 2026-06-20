use std::collections::HashMap;

use inkwell::{
    OptimizationLevel,
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    execution_engine::ExecutionEngine,
    module::Module,
    values::{BasicValueEnum, FunctionValue},
};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionBody, FunctionDef, Item, Param, Stmt, UnOp},
    error::CompileError,
    span::Symbol,
};

mod expr;
mod membership;
mod loops;

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

/// Compile every function in `items` into a single JIT module.
///
/// Two-pass: all functions are declared first so that forward and mutual
/// calls resolve, then bodies are compiled in order.
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
