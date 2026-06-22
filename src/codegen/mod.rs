use std::collections::{HashMap, HashSet};

use inkwell::{
    AddressSpace,
    OptimizationLevel,
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    execution_engine::ExecutionEngine,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{AggregateValueEnum, BasicValueEnum, FunctionValue},
};

use crate::{
    ast::{BinOp, DefKind, Expr, ExprKind, FunctionBody, FunctionDef, Item, Param, Stmt, UnOp},
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
    /// Maps each declared function name to its first-signature range expression.
    /// Used by `compile_try` to determine which named error sets `?` should
    /// propagate for that callee.
    fn_ranges: HashMap<String, Expr>,
    /// Pre-expanded integer values for user-defined named sets whose definitions
    /// are set literals (e.g. `HTTPError = {400, 503}` → `[400, 503]`).
    /// Used by `compile_try` and `compile_membership` for named error set checks.
    user_set_vals: HashMap<String, Vec<i64>>,
    /// Names of all `distinct` sets in the file (e.g. `"Litre"`, `"Kelvin"`).
    /// Used to detect auto-generated constructors like `litre(x)` → identity.
    distinct_names: HashSet<String>,
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
            fn_ranges: HashMap::new(),
            user_set_vals: HashMap::new(),
            distinct_names: HashSet::new(),
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
        param_kinds: &[Kind],
        return_kind: Kind,
    ) -> FunctionValue<'ctx> {
        let i64_type = self.context.i64_type();
        // Tuple params use their natural struct type; all scalar params are i64.
        let param_types: Vec<_> = if param_kinds.is_empty() {
            params.iter().map(|_| i64_type.into()).collect()
        } else {
            param_kinds.iter().map(|k| match k {
                Kind::Tuple(_) => self.kind_to_llvm_type(k).into(),
                _ => i64_type.into(),
            }).collect()
        };
        let fn_val = match &return_kind {
            Kind::Tuple(_) => {
                let ret_type = self.kind_to_llvm_type(&return_kind);
                self.module.add_function(name, ret_type.fn_type(&param_types, false), None)
            }
            _ => {
                self.module.add_function(name, i64_type.fn_type(&param_types, false), None)
            }
        };
        self.fn_return_kinds.insert(name.to_owned(), return_kind);
        fn_val
    }

    /// Map a Kind to the natural LLVM type used inside structs and as tuple ABI types.
    /// Scalars: Int/Set → i64, Bool → i1.  Tuple → struct of element types.
    pub(crate) fn kind_to_llvm_type(&self, kind: &Kind) -> BasicTypeEnum<'ctx> {
        match kind {
            Kind::Int | Kind::Set(_) => self.context.i64_type().into(),
            Kind::Bool => self.context.bool_type().into(),
            Kind::Tuple(elems) => {
                let types: Vec<BasicTypeEnum<'ctx>> = elems.iter()
                    .map(|k| self.kind_to_llvm_type(k))
                    .collect();
                self.context.struct_type(&types, false).into()
            }
        }
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
        for ((param, llvm_param), kind) in params
            .iter()
            .zip(function.get_param_iter())
            .zip(param_kinds.iter())
        {
            llvm_param.set_name(&param.name.0);
            let entry = if *kind == Kind::Bool {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        llvm_param.into_int_value(),
                        self.context.bool_type(),
                        "bool_param",
                    )
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                (i1_val.into(), Kind::Bool)
            } else if matches!(kind, Kind::Tuple(_)) {
                (llvm_param, kind.clone())
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
            // Tuples return as struct values directly; Int/Set return as i64.
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
        for ((param, llvm_param), kind) in params
            .iter()
            .zip(function.get_param_iter())
            .zip(param_kinds.iter())
        {
            llvm_param.set_name(&param.name.0);
            let entry = if *kind == Kind::Bool {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        llvm_param.into_int_value(),
                        self.context.bool_type(),
                        "bool_param",
                    )
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                (i1_val.into(), Kind::Bool)
            } else if matches!(kind, Kind::Tuple(_)) {
                (llvm_param, kind.clone())
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
            Some((val, Kind::Int)) | Some((val, Kind::Set(_))) | Some((val, Kind::Tuple(_))) => val,
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
        let function = self.declare_function(name, params, &all_int, Kind::Int);
        self.compile_function_body(function, params, &all_int, body, false, &Env::new())
    }

    /// Borrow the underlying LLVM module (useful for tests and manual IR construction).
    pub fn module(&self) -> &Module<'ctx> {
        &self.module
    }

    /// Declare all Cantor runtime functions as external symbols in the module.
    ///
    /// Must be called before compiling any code that uses runtime sets.
    /// `into_jit_engine` will then register the actual function pointers so
    /// the JIT can resolve the calls.
    pub fn declare_runtime_functions(&mut self) {
        let i64t = self.context.i64_type();
        let void = self.context.void_type();
        let ii   = &[i64t.into(), i64t.into()] as &[_]; // (set_ptr, val) -> ...
        let i    = &[i64t.into()] as &[_];               // (set_ptr) -> i64

        // Set(Int) ABI
        self.module.add_function("cantor_set_new_i64",      i64t.fn_type(&[], false),  None);
        self.module.add_function("cantor_set_insert_i64",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_contains_i64", i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_size_i64",     i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_set_get_i64",      i64t.fn_type(ii,   false), None);

        // Set(Bool) ABI — booleans passed as i64 (0/1) at the boundary
        self.module.add_function("cantor_set_new_bool",      i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_set_insert_bool",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_contains_bool", i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_size_bool",     i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_set_get_bool",      i64t.fn_type(ii,   false), None);
    }

    /// Consume the compiler and hand the module to a JIT engine.
    ///
    /// Any runtime functions declared via `declare_runtime_functions` are
    /// registered with the engine via `add_global_mapping` so the JIT can
    /// resolve calls to them without dynamic library lookup.
    pub fn into_jit_engine(self) -> Result<ExecutionEngine<'ctx>, String> {
        use crate::runtime;

        // Collect (FunctionValue, address) pairs while we still have the module.
        // FunctionValue<'ctx> is tied to the LLVM context lifetime, not to the
        // module, so these remain valid after the module is consumed below.
        let mappings: Vec<(FunctionValue<'ctx>, usize)> = {
            let rt: &[(&str, usize)] = &[
                ("cantor_set_new_i64",       runtime::cantor_set_new_i64      as usize),
                ("cantor_set_insert_i64",    runtime::cantor_set_insert_i64   as usize),
                ("cantor_set_contains_i64",  runtime::cantor_set_contains_i64 as usize),
                ("cantor_set_size_i64",      runtime::cantor_set_size_i64     as usize),
                ("cantor_set_get_i64",       runtime::cantor_set_get_i64      as usize),
                ("cantor_set_new_bool",      runtime::cantor_set_new_bool     as usize),
                ("cantor_set_insert_bool",   runtime::cantor_set_insert_bool  as usize),
                ("cantor_set_contains_bool", runtime::cantor_set_contains_bool as usize),
                ("cantor_set_size_bool",     runtime::cantor_set_size_bool    as usize),
                ("cantor_set_get_bool",      runtime::cantor_set_get_bool     as usize),
            ];
            rt.iter()
                .filter_map(|&(name, addr)| self.module.get_function(name).map(|f| (f, addr)))
                .collect()
        }; // borrow of self.module ends here

        let ee = self.module
            .create_jit_execution_engine(OptimizationLevel::None)
            .map_err(|e| e.to_string())?;

        for (fn_val, addr) in mappings {
            unsafe { ee.add_global_mapping(&fn_val, addr); }
        }

        Ok(ee)
    }

    pub fn print_ir(&self) {
        self.module.print_to_stderr();
    }
}

/// True if the range expression can produce a failure value at runtime.
///
/// This covers both the traditional `| Fail` union and the new `!!` error-union
/// operator (which encodes errors as FAIL_SENTINEL + payload + 1).
pub fn range_contains_fail(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::Var(sym) => sym.0 == "Fail",
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            range_contains_fail(lhs) || range_contains_fail(rhs)
        }
        // `A !! B` always permits runtime failure.
        ExprKind::BinOp { op: BinOp::ErrorUnion, .. } => true,
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
/// Three-pass compilation (constants → declarations → bodies) into a `Compiler`.
/// Both `compile_file` and `compile_to_ir` delegate here.
fn compile_items<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
) -> Result<Compiler<'ctx>, CompileError> {
    let mut compiler = Compiler::new(ctx, "cantor");
    compiler.declare_runtime_functions();

    // Pass 0 — evaluate scalar constants and build a shared env of inlined values.
    // Set-definition NameDefs (e.g. `HTTPError = {400, 503}`) are silently skipped
    // here because they have no scalar value to inline into function bodies; they
    // are collected separately into `user_set_vals` below.
    let mut const_vals: HashMap<Symbol, i64> = HashMap::new();
    for item in items {
        if let Item::NameDef(def) = item {
            if let Ok(val) = eval_const(&def.value, &const_vals) {
                const_vals.insert(def.name.clone(), val);
            }
        }
    }

    // Collect integer-value lists for set-literal NameDefs so that
    // `compile_membership` and `compile_try` can reason about named error sets
    // (e.g. `HTTPError = {400, 503}`) at compile time.
    let mut user_set_vals: HashMap<String, Vec<i64>> = HashMap::new();
    for item in items {
        if let Item::NameDef(def) = item {
            if let ExprKind::SetLit(elements) = &def.value.kind {
                let vals: Option<Vec<i64>> = elements
                    .iter()
                    .map(|e| match &e.kind {
                        ExprKind::IntLit(n) => Some(*n),
                        ExprKind::Var(sym) => const_vals.get(sym).copied(),
                        _ => None,
                    })
                    .collect();
                if let Some(v) = vals {
                    user_set_vals.insert(def.name.0.clone(), v);
                }
            }
        }
    }
    compiler.user_set_vals = user_set_vals;

    compiler.distinct_names = items
        .iter()
        .filter_map(|item| match item {
            Item::NameDef(def) if def.kind == DefKind::Distinct => Some(def.name.0.clone()),
            _ => None,
        })
        .collect();

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
                let first_sig = def.sigs.first();
                let p_kinds: Vec<Kind> = first_sig
                    .map(|s| param_kinds(s, def.params.len()))
                    .unwrap_or_else(|| vec![Kind::Int; def.params.len()]);
                let ret_kind = first_sig
                    .map(|s| range_kind(&s.range))
                    .unwrap_or(Kind::Int);
                let fn_val = compiler.declare_function(&def.name.0, &def.params, &p_kinds, ret_kind);
                // Record the range expression so `compile_try` can determine what
                // error values `?` should propagate for this callee.
                if let Some(sig) = first_sig {
                    compiler.fn_ranges.insert(def.name.0.clone(), sig.range.clone());
                }
                Some((fn_val, def))
            }
            Item::NameDef(_) => None,
        })
        .collect();

    // Pass 2 — compile bodies with constants available.
    for (fn_val, def) in decls {
        let is_fallible = def.sigs.iter().any(|s| range_contains_fail(&s.range));
        let p_kinds: Vec<Kind> = def
            .sigs
            .first()
            .map(|s| param_kinds(s, def.params.len()))
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

    // If `main` returns a tuple, emit an ABI-safe `cantor_main_into(ptr)` trampoline
    // that calls main and stores each scalar leaf into the caller-supplied buffer.
    if let Some(main_fn) = compiler.module.get_function("main") {
        let ret_kind = compiler.fn_return_kinds.get("main").cloned().unwrap_or(Kind::Int);
        if let Kind::Tuple(_) = &ret_kind {
            compiler.emit_tuple_main_trampoline(main_fn, &ret_kind)?;
        }
    }

    Ok(compiler)
}

impl<'ctx> Compiler<'ctx> {
    /// Emit `void @cantor_main_into(ptr %out)` which calls `main()` (struct return)
    /// and stores every i64 leaf of the tuple into the caller-supplied buffer.
    /// Booleans are zero-extended to i64 before storing.
    fn emit_tuple_main_trampoline(
        &self,
        main_fn: FunctionValue<'ctx>,
        ret_kind: &Kind,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();
        let ptr_t = self.context.ptr_type(AddressSpace::default());
        let fn_type = self.context.void_type().fn_type(&[ptr_t.into()], false);
        let trampoline = self.module.add_function("cantor_main_into", fn_type, None);

        let bb = self.context.append_basic_block(trampoline, "entry");
        self.builder.position_at_end(bb);

        let out_ptr = trampoline.get_nth_param(0).unwrap().into_pointer_value();

        let call = self.builder
            .build_call(main_fn, &[], "main_result")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let result = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("main returned void in trampoline".into()))?;

        let mut leaf_idx = 0usize;
        Self::trampoline_store_leaves(
            &self.builder, &self.context, result, ret_kind, out_ptr, i64t, &mut leaf_idx,
        )?;

        self.builder
            .build_return(None)
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        Ok(())
    }

    fn trampoline_store_leaves(
        builder: &inkwell::builder::Builder<'ctx>,
        ctx: &'ctx Context,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
        out_ptr: inkwell::values::PointerValue<'ctx>,
        i64t: inkwell::types::IntType<'ctx>,
        leaf_idx: &mut usize,
    ) -> Result<(), CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());
        match kind {
            Kind::Bool => {
                let wide = builder.build_int_z_extend(val.into_int_value(), i64t, "bl").map_err(err)?;
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    // Safety: GEP into a caller-allocated i64 array; index is in-bounds
                    // because run_main allocates n_leaves elements.
                    unsafe { builder.build_gep(i64t, out_ptr, &[idx], "gp").map_err(err)? }
                };
                builder.build_store(ptr, wide).map_err(err)?;
                *leaf_idx += 1;
            }
            Kind::Int | Kind::Set(_) => {
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    // Safety: same as above.
                    unsafe { builder.build_gep(i64t, out_ptr, &[idx], "gp").map_err(err)? }
                };
                builder.build_store(ptr, val.into_int_value()).map_err(err)?;
                *leaf_idx += 1;
            }
            Kind::Tuple(elem_kinds) => {
                let sv = AggregateValueEnum::StructValue(val.into_struct_value());
                for (i, ek) in elem_kinds.iter().enumerate() {
                    let elem = builder.build_extract_value(sv, i as u32, "te").map_err(err)?;
                    Self::trampoline_store_leaves(builder, ctx, elem, ek, out_ptr, i64t, leaf_idx)?;
                }
            }
        }
        Ok(())
    }
}

/// Compile a parsed file to a JIT execution engine.
pub fn compile_file<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
) -> Result<ExecutionEngine<'ctx>, CompileError> {
    compile_items(ctx, items)?
        .into_jit_engine()
        .map_err(CompileError::Internal)
}

/// Compile a parsed file and return the LLVM IR as a string (no JIT).
///
/// Useful in tests to assert whether something was handled at compile time
/// (no runtime calls in the IR) or at runtime (runtime calls present).
pub fn compile_to_ir<'ctx>(ctx: &'ctx Context, items: &[Item]) -> Result<String, CompileError> {
    let compiler = compile_items(ctx, items)?;
    Ok(compiler.module().print_to_string().to_string())
}
