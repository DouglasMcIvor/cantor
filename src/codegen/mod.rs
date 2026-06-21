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
    kind::{Kind, param_kinds, range_kind},
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

type Env<'ctx> = HashMap<Symbol, (BasicValueEnum<'ctx>, Kind)>;

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
    /// Maps each declared function name to its return Kind so `compile_call`
    /// can truncate the i64 result back to i1 for Bool-returning functions.
    fn_return_kinds: HashMap<String, Kind>,
}

impl<'ctx> Compiler<'ctx> {
    pub fn new(context: &'ctx Context, name: &str) -> Self {
        Self {
            context,
            module: context.create_module(name),
            builder: context.create_builder(),
            current_fn: None,
            fail_bb: None,
            fn_return_kinds: HashMap::new(),
        }
    }

    /// Add a function declaration to the module (no body yet).
    ///
    /// All parameters and the return value use i64 (uniform ABI); Bool values
    /// are widened to i64 at function boundaries and truncated back inside the
    /// body.  `return_kind` is recorded in [`fn_return_kinds`] so call sites
    /// can restore the correct Kind after the call.
    pub fn declare_function(
        &mut self,
        name: &str,
        params: &[Param],
        return_kind: Kind,
    ) -> FunctionValue<'ctx> {
        let i64_type = self.context.i64_type();
        let param_types: Vec<_> = params.iter().map(|_| i64_type.into()).collect();
        let fn_type = i64_type.fn_type(&param_types, false);
        let fn_val = self.module.add_function(name, fn_type, None);
        self.fn_return_kinds.insert(name.to_owned(), return_kind);
        fn_val
    }

    /// Compile the body of an already-declared function (expression body).
    ///
    /// Bool-domain parameters arrive as i64 and are truncated to i1 in the
    /// local env.  The return value is zero-extended to i64 so all functions
    /// share a uniform `fn(i64, …) -> i64` ABI.
    pub fn compile_function_body(
        &mut self,
        function: FunctionValue<'ctx>,
        params: &[Param],
        param_kinds: &[Kind],
        body: &Expr,
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

        let mut env: Env = const_env.clone();
        for ((param, llvm_param), &kind) in params
            .iter()
            .zip(function.get_param_iter())
            .zip(param_kinds.iter())
        {
            llvm_param.set_name(&param.name.0);
            let entry = if kind == Kind::Bool {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        llvm_param.into_int_value(),
                        self.context.bool_type(),
                        "bool_param",
                    )
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                (i1_val.into(), Kind::Bool)
            } else {
                (llvm_param, Kind::Int)
            };
            env.insert(param.name.clone(), entry);
        }

        let (val, ty) = self.compile_expr(body, &env)?;

        let i64_type = self.context.i64_type();
        let ret_val = if ty == Kind::Bool {
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
        param_kinds: &[Kind],
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

        let mut env: Env = const_env.clone();
        for ((param, llvm_param), &kind) in params
            .iter()
            .zip(function.get_param_iter())
            .zip(param_kinds.iter())
        {
            llvm_param.set_name(&param.name.0);
            let entry = if kind == Kind::Bool {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        llvm_param.into_int_value(),
                        self.context.bool_type(),
                        "bool_param",
                    )
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                (i1_val.into(), Kind::Bool)
            } else {
                (llvm_param, Kind::Int)
            };
            env.insert(param.name.clone(), entry);
        }

        let return_val = self.compile_stmts(stmts, &mut env, &HashMap::new())?;

        let i64_type = self.context.i64_type();
        let ret_val = match return_val {
            Some((val, Kind::Bool)) => self
                .builder
                .build_int_z_extend(val.into_int_value(), i64_type, "bool_to_i64")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into(),
            Some((val, Kind::Int)) | Some((val, Kind::Set(_))) => val,
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
    /// Convenience wrapper used by tests; assumes all params and return are
    /// `Kind::Int`.
    pub fn compile_function(
        &mut self,
        name: &str,
        params: &[Param],
        body: &Expr,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        let all_int: Vec<Kind> = vec![Kind::Int; params.len()];
        let function = self.declare_function(name, params, Kind::Int);
        self.compile_function_body(function, params, &all_int, body, false, &Env::new())
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
/// Three-pass: constants evaluated first, then all functions declared (so
/// forward/mutual calls resolve), then bodies compiled.
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
            (sym.clone(), (llvm_val.into(), Kind::Int))
        })
        .collect();

    // Pass 1 — declare all function signatures so forward calls resolve.
    // Param and return Kinds are derived from the first signature; overloaded
    // functions must agree on the Kind of each position.
    let decls: Vec<(FunctionValue<'ctx>, &FunctionDef)> = items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => {
                let ret_kind = def
                    .sigs
                    .first()
                    .map(|s| range_kind(&s.range))
                    .unwrap_or(Kind::Int);
                let fn_val = compiler.declare_function(&def.name.0, &def.params, ret_kind);
                Some((fn_val, def))
            }
            Item::ConstDef(_) => None,
        })
        .collect();

    // Pass 2 — compile bodies with constants available.
    for (fn_val, def) in decls {
        let is_fallible = def.sigs.iter().any(|s| range_contains_fail(&s.range));
        let p_kinds: Vec<Kind> = def
            .sigs
            .first()
            .map(|s| param_kinds(s))
            .unwrap_or_else(|| vec![Kind::Int; def.params.len()]);

        match &def.body {
            FunctionBody::Expr(e) => {
                compiler.compile_function_body(
                    fn_val, &def.params, &p_kinds, e, is_fallible, &const_env,
                )?;
            }
            FunctionBody::Block(stmts) => {
                compiler.compile_block_body(
                    fn_val, &def.params, &p_kinds, stmts, is_fallible, &const_env,
                )?;
            }
        }
    }

    compiler
        .into_jit_engine()
        .map_err(|e| CompileError::Internal(e))
}
