use std::collections::{HashMap, HashSet};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{AggregateValueEnum, BasicValueEnum, FunctionValue},
};

use crate::{
    ast::{BinOp, DefKind, Expr, ExprKind, Item, Param, UnOp},
    error::CompileError,
    kind::Kind,
    semantics::{
        elaborate::elaborate,
        tree::{SemExpr, SemFunctionBody, SemItem, SemStmt},
    },
    span::{Span, Symbol},
};

mod arith;
mod blocks;
mod coerce;
mod expr;
mod expr_vec;
mod jit;
mod loops;
mod membership;
mod overload_dispatch;
mod runtime_decls;
mod trampoline;
pub mod wire;

use wire::tagged_union_leaf_count;

pub use jit::{compile_constrained, compile_file};

/// Sentinel used only at the JIT runner boundary (main.rs → __cantor_main_runner).
/// Not part of general codegen; all internal functions use `{i1, i64}` structs.
const JIT_RUNNER_SENTINEL: i64 = i64::MIN;

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
    fn_ranges: HashMap<String, SemExpr>,
    /// Pre-expanded integer values for user-defined named sets whose definitions
    /// are set literals (e.g. `HTTPError = {400, 503}` → `[400, 503]`).
    /// Used by `compile_try` and `compile_membership` for named error set checks.
    user_set_vals: HashMap<String, Vec<i64>>,
    /// Names of all `distinct` sets in the file (e.g. `"Litre"`, `"Kelvin"`).
    /// Used to detect auto-generated constructors like `litre(x)` → identity.
    distinct_names: HashSet<String>,
    /// Maps each declared function name to the runtime Kind of each parameter.
    /// Populated in pass 1 alongside `fn_return_kinds`; used at call sites to
    /// box scalar/tuple arguments when the callee expects a `Kind::Vector`.
    fn_param_kinds: HashMap<String, Vec<Kind>>,
    /// Maps each declared function name to its first-signature per-parameter
    /// domain set expressions. Used by `coerce_call_arg` the same way
    /// `fn_ranges` is used by `coerce_tagged_union_return`: to disambiguate
    /// which arm of a `+`-typed parameter a scalar call argument belongs to.
    fn_param_set_exprs: HashMap<String, Vec<SemExpr>>,
    /// int-soundness-plan phase 1: per-arithmetic-node-span "proved not to
    /// overflow i64" verdicts from `ConstrainedTree::overflow_checks`. Empty
    /// (via `compile_items`/`compile_file`, which have no solver-verified
    /// tree — the REPL, `llvm-ir` on an unproved file) means every arithmetic
    /// op is conservatively treated as unproved: `.get(span).copied().unwrap_or(false)`.
    overflow_checks: HashMap<Span, bool>,
    /// `(path, src)` for formatting an overflow-abort message with a
    /// `path:line:col` prefix, matching `main.rs`'s `print_compile_error`.
    /// `None` when there's no single coherent source string to point at
    /// (`compile_items`/`compile_file` — see the REPL's own note on why
    /// span→line:col can't be trusted there).
    overflow_ctx: Option<(String, String)>,
    /// int-soundness-plan phase 2: one entry per name that has more than one
    /// `FunctionDef` in the file (an overload set) — absent for every
    /// ordinary, non-overloaded name (the overwhelming common case, compiled
    /// exactly as before). Indexed the same way
    /// `ConstrainedTree::overload_resolution` is: position in file order
    /// among this name's `FunctionDef`s.
    overload_dispatch: HashMap<String, Vec<OverloadEntry>>,
    /// Per-call-node-span statically-resolved overload index, from
    /// `ConstrainedTree::overload_resolution`. Empty via
    /// `compile_items`/`compile_file`/REPL/`llvm-ir` (no solver-verified
    /// tree), same "no tree ⇒ conservative" default as `overflow_checks`.
    overload_resolution: HashMap<Span, usize>,
}

/// One candidate in an overload set — see `Compiler::overload_dispatch`.
struct OverloadEntry {
    /// The LLVM function name this candidate was declared under
    /// (`{name}__ov{index}`).
    mangled_name: String,
    arity: usize,
    /// This candidate's first declared signature's per-parameter domain
    /// (used for the runtime dispatch chain's membership tests).
    ///
    /// TODO: a candidate with more than one of its own signatures (today's
    /// existing multiple-signatures-one-body feature, combined with
    /// overloading) only has its *first* signature's domain checked at
    /// runtime here — matches this codebase's existing precedent
    /// (`Compiler::fn_param_set_exprs` has always stored only the first
    /// signature's domain, even before overloading existed) but is worth
    /// widening to an OR-across-signatures check if that combination shows
    /// up in practice.
    domain_parts: Vec<SemExpr>,
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
            fn_param_set_exprs: HashMap::new(),
            fn_param_kinds: HashMap::new(),
            overflow_checks: HashMap::new(),
            overflow_ctx: None,
            overload_dispatch: HashMap::new(),
            overload_resolution: HashMap::new(),
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
        // Tuple and TaggedUnion params use their natural struct type; scalars are i64.
        let param_types: Vec<_> = if param_kinds.is_empty() {
            params.iter().map(|_| i64_type.into()).collect()
        } else {
            param_kinds
                .iter()
                .map(|k| match k {
                    Kind::Tuple(_) | Kind::TaggedUnion(_) => self.kind_to_llvm_type(k).into(),
                    _ => i64_type.into(),
                })
                .collect()
        };
        let fn_val = match &return_kind {
            Kind::Tuple(_) | Kind::TaggedUnion(_) => {
                let ret_type = self.kind_to_llvm_type(&return_kind);
                self.module
                    .add_function(name, ret_type.fn_type(&param_types, false), None)
            }
            _ => self
                .module
                .add_function(name, i64_type.fn_type(&param_types, false), None),
        };
        self.fn_return_kinds.insert(name.to_owned(), return_kind);
        self.fn_param_kinds
            .insert(name.to_owned(), param_kinds.to_vec());
        fn_val
    }

    /// Map a Kind to the natural LLVM type used inside structs and as tuple ABI types.
    /// Scalars: Int/Set/Union → i64, Bool → i1.  Tuple → struct of element types.
    /// TaggedUnion → `{ i32 tag, i64, …, i64 }` with enough i64 slots for the widest arm.
    pub(crate) fn kind_to_llvm_type(&self, kind: &Kind) -> BasicTypeEnum<'ctx> {
        match kind {
            Kind::Int | Kind::Int64 | Kind::Set(_) => self.context.i64_type().into(),
            Kind::Bool | Kind::Fail => self.context.bool_type().into(),
            // Plain i32 register — wraps by construction via ordinary LLVM
            // i32 arithmetic (two's-complement is the default), no nsw/nuw
            // flags (docs/wrapping-and-quotient-sets-plan.md).
            Kind::Signed32 | Kind::Unsigned32 => self.context.i32_type().into(),
            // Also a plain i32 register (a Unicode scalar value) — unlike
            // Signed32/Unsigned32, not every bit pattern is valid, but
            // validity is a proof obligation checked once at `char(n)`
            // construction, not an LLVM-level property.
            Kind::Char => self.context.i32_type().into(),
            Kind::Tuple(elems) => {
                let types: Vec<BasicTypeEnum<'ctx>> =
                    elems.iter().map(|k| self.kind_to_llvm_type(k)).collect();
                self.context.struct_type(&types, false).into()
            }
            Kind::TaggedUnion(arms) => {
                let n = tagged_union_leaf_count(arms);
                let i32t: BasicTypeEnum = self.context.i32_type().into();
                let i64t: BasicTypeEnum = self.context.i64_type().into();
                let mut fields = vec![i32t];
                fields.extend(std::iter::repeat_n(i64t, n));
                self.context.struct_type(&fields, false).into()
            }
            // Vector is an i64 pointer-as-i64 (same wire type as Set).
            Kind::Vector(_) => self.context.i64_type().into(),
        }
    }

    /// Returns the `{i1, i64}` struct type used for all fallible function returns.
    pub(crate) fn fail_struct_type(&self) -> inkwell::types::StructType<'ctx> {
        self.context.struct_type(
            &[
                self.context.bool_type().into(),
                self.context.i64_type().into(),
            ],
            false,
        )
    }

    /// Serialise `val : arm_kind` into the i64 leaf fields of a tagged-union
    /// struct, starting at `field_idx` (1-based; field 0 is the tag).
    fn insert_kind_leaves(
        &self,
        agg: &mut AggregateValueEnum<'ctx>,
        val: BasicValueEnum<'ctx>,
        arm_kind: &Kind,
        field_idx: &mut u32,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        match arm_kind {
            Kind::Int | Kind::Int64 | Kind::Set(_) => {
                *agg = self
                    .builder
                    .build_insert_value(*agg, val.into_int_value(), *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
            Kind::Bool | Kind::Fail => {
                let wide = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "tu_lb")
                    .map_err(err)?;
                *agg = self
                    .builder
                    .build_insert_value(*agg, wide, *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
            Kind::Signed32 => {
                let wide = self
                    .builder
                    .build_int_s_extend(val.into_int_value(), i64t, "tu_ls32")
                    .map_err(err)?;
                *agg = self
                    .builder
                    .build_insert_value(*agg, wide, *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
            Kind::Unsigned32 | Kind::Char => {
                let wide = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "tu_lu32")
                    .map_err(err)?;
                *agg = self
                    .builder
                    .build_insert_value(*agg, wide, *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
            Kind::Tuple(elems) => {
                let sv = AggregateValueEnum::StructValue(val.into_struct_value());
                for (i, ek) in elems.iter().enumerate() {
                    let elem = self
                        .builder
                        .build_extract_value(sv, i as u32, "tu_te")
                        .map_err(err)?;
                    self.insert_kind_leaves(agg, elem, ek, field_idx)?;
                }
            }
            Kind::TaggedUnion(_) => {
                return Err(CompileError::ice(
                    "insert_kind_leaves: nested TaggedUnion not yet supported",
                ));
            }
            // Vector is an i64 pointer — insert it like Int/Set.
            Kind::Vector(_) => {
                *agg = self
                    .builder
                    .build_insert_value(*agg, val.into_int_value(), *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
        }
        Ok(())
    }

    /// Build a `{i1=0, i64=payload}` success-tagged struct.
    pub(crate) fn build_success_struct(
        &self,
        payload: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let zero_i1 = self.context.bool_type().const_int(0, false);
        let s = self.fail_struct_type().get_undef();
        let s = self
            .builder
            .build_insert_value(s, zero_i1, 0, "sv_flag")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_struct_value();
        let s = self
            .builder
            .build_insert_value(s, payload, 1, "sv_payload")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_struct_value();
        Ok(s.into())
    }

    /// Build a `{i1=1, i64=payload}` fail-tagged struct.
    pub(crate) fn build_fail_struct(
        &self,
        payload: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let one_i1 = self.context.bool_type().const_int(1, false);
        let s = self.fail_struct_type().get_undef();
        let s = self
            .builder
            .build_insert_value(s, one_i1, 0, "fv_flag")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_struct_value();
        let s = self
            .builder
            .build_insert_value(s, payload, 1, "fv_payload")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_struct_value();
        Ok(s.into())
    }

    /// Coerce a value to `{i1=0, i64=val}` when one branch of an `if` is a fail struct.
    /// Fail structs pass through unchanged.
    pub(crate) fn coerce_to_fail_struct(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if matches!(kind, Kind::Tuple(e) if e.first() == Some(&Kind::Fail)) {
            return Ok(val);
        }
        let payload = match kind {
            Kind::Bool
            | Kind::Int
            | Kind::Int64
            | Kind::Set(_)
            | Kind::Signed32
            | Kind::Unsigned32 => self.widen_scalar_to_i64(val, kind, "coerce_bool")?,
            _ => {
                return Err(CompileError::ice(
                    "cannot coerce value to fail struct: unsupported kind",
                ));
            }
        };
        self.build_success_struct(payload)
    }

    /// Widen a scalar ABI-boundary-crossing value up to i64: `Bool` (i1)
    /// zero-extends, `Signed32`/`Unsigned32` (i32) sign-/zero-extend
    /// respectively (docs/wrapping-and-quotient-sets-plan.md — mirrors the
    /// existing `Bool` widen exactly, just with a different width/extend
    /// kind), `Char` (i32) zero-extends (same as `Unsigned32` — codepoints
    /// are non-negative), anything already i64-shaped passes through
    /// unchanged.
    fn widen_scalar_to_i64(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
        name: &str,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let i64t = self.context.i64_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        Ok(match kind {
            Kind::Bool => self
                .builder
                .build_int_z_extend(val.into_int_value(), i64t, name)
                .map_err(err)?
                .into(),
            Kind::Signed32 => self
                .builder
                .build_int_s_extend(val.into_int_value(), i64t, name)
                .map_err(err)?
                .into(),
            Kind::Unsigned32 | Kind::Char => self
                .builder
                .build_int_z_extend(val.into_int_value(), i64t, name)
                .map_err(err)?
                .into(),
            _ => val,
        })
    }

    /// Inverse of `widen_scalar_to_i64`: narrow an incoming i64 parameter
    /// down to its declared Kind's natural register width — `Bool` (i1),
    /// `Signed32`/`Unsigned32`/`Char` (i32, same truncation regardless of
    /// signedness — sign only matters for how the bits are *interpreted*,
    /// e.g. `bvslt` vs `bvult` at the solver layer, comparisons/`from()` at
    /// codegen, never for the truncation itself). Anything else passes
    /// through unchanged (already i64-shaped).
    fn narrow_i64_param(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
        name: &str,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        Ok(match kind {
            Kind::Bool => self
                .builder
                .build_int_truncate(val.into_int_value(), self.context.bool_type(), name)
                .map_err(err)?
                .into(),
            Kind::Signed32 | Kind::Unsigned32 | Kind::Char => self
                .builder
                .build_int_truncate(val.into_int_value(), self.context.i32_type(), name)
                .map_err(err)?
                .into(),
            _ => val,
        })
    }

    /// Wrap a return value for a fallible function if needed.
    ///
    /// - Already a fail struct → pass through (e.g. from `FailLit`, `compile_try`)
    /// - Bool/Signed32/Unsigned32/Char in non-fallible function → widen to i64
    /// - Any other value in non-fallible function → pass through
    /// - Any non-struct value in fallible function → wrap in `{i1=0, i64=val}`
    pub(crate) fn wrap_return_value(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if self.fail_bb.is_none() {
            // Non-fallible: widen Bool/Signed32/Unsigned32 to i64 and pass
            // everything else through.
            return self.widen_scalar_to_i64(val, kind, "ret_wide");
        }
        // Fallible function: ensure the value is a {i1, i64} struct.
        if matches!(kind, Kind::Tuple(e) if e.first() == Some(&Kind::Fail)) {
            return Ok(val); // already a fail struct
        }
        let payload = self.widen_scalar_to_i64(val, kind, "ret_wide")?;
        self.build_success_struct(payload)
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
        body: &SemExpr,
        is_fallible: bool,
        const_env: &Env<'ctx>,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        self.current_fn = Some(function);

        let entry = self.context.append_basic_block(function, "entry");

        self.fail_bb = if is_fallible {
            let bb = self.context.append_basic_block(function, "fail");
            self.builder.position_at_end(bb);
            // Bare assert failure returns {i1=1, i64=0} — no typed error code.
            let fail_struct = self.fail_struct_type().const_named_struct(&[
                self.context.bool_type().const_int(1, false).into(),
                self.context.i64_type().const_int(0, false).into(),
            ]);
            self.builder
                .build_return(Some(&BasicValueEnum::StructValue(fail_struct)))
                .map_err(|e| CompileError::ice(e.to_string()))?;
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
            // int-soundness-plan phase 3: preserving the declared Kind here
            // (not hardcoding `Kind::Int`) is what lets a compiler-generated
            // `Int64` overload's parameter be correctly seen as raw/untagged
            // downstream, distinct from an ordinary `Kind::Int` (tagged)
            // parameter — both are the same `i64` LLVM type, so no other
            // change is needed for those. Bool/Signed32/Unsigned32 do need
            // narrowing from the uniform i64 ABI down to their native width.
            let entry = (
                self.narrow_i64_param(llvm_param, kind, "param_narrow")?,
                kind.clone(),
            );
            env.insert(param.name.clone(), entry);
        }

        let (val, ty) = self.compile_expr(body, &env)?;
        let (val, ty) = self.coerce_int_return(val, ty, function)?;
        let (val, ty) = self.coerce_vector_return(val, ty, function)?;
        let (val, ty) = self.coerce_tagged_union_return(val, ty, function)?;
        let ret_val = self.wrap_return_value(val, &ty)?;

        self.builder
            .build_return(Some(&ret_val))
            .map_err(|e| CompileError::ice(e.to_string()))?;

        Ok(function)
    }

    /// Compile the body of an already-declared function (block body).
    pub fn compile_block_body(
        &mut self,
        function: FunctionValue<'ctx>,
        params: &[Param],
        param_kinds: &[Kind],
        stmts: &[SemStmt],
        is_fallible: bool,
        const_env: &Env<'ctx>,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        self.current_fn = Some(function);

        let entry = self.context.append_basic_block(function, "entry");

        self.fail_bb = if is_fallible {
            let bb = self.context.append_basic_block(function, "fail");
            self.builder.position_at_end(bb);
            // Bare assert failure returns {i1=1, i64=0} — no typed error code.
            let fail_struct = self.fail_struct_type().const_named_struct(&[
                self.context.bool_type().const_int(1, false).into(),
                self.context.i64_type().const_int(0, false).into(),
            ]);
            self.builder
                .build_return(Some(&BasicValueEnum::StructValue(fail_struct)))
                .map_err(|e| CompileError::ice(e.to_string()))?;
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
            // int-soundness-plan phase 3: preserving the declared Kind here
            // (not hardcoding `Kind::Int`) is what lets a compiler-generated
            // `Int64` overload's parameter be correctly seen as raw/untagged
            // downstream, distinct from an ordinary `Kind::Int` (tagged)
            // parameter — both are the same `i64` LLVM type, so no other
            // change is needed for those. Bool/Signed32/Unsigned32 do need
            // narrowing from the uniform i64 ABI down to their native width.
            let entry = (
                self.narrow_i64_param(llvm_param, kind, "param_narrow")?,
                kind.clone(),
            );
            env.insert(param.name.clone(), entry);
        }

        let return_val = self.compile_stmts(stmts, &mut env, &HashMap::new())?;

        match return_val {
            Some((val, kind)) => {
                let (val, kind) = self.coerce_int_return(val, kind, function)?;
                let (val, kind) = self.coerce_vector_return(val, kind, function)?;
                let (val, kind) = self.coerce_tagged_union_return(val, kind, function)?;
                let ret_val = self.wrap_return_value(val, &kind)?;
                self.builder
                    .build_return(Some(&ret_val))
                    .map_err(|e| CompileError::ice(e.to_string()))?;
            }
            None => {
                // An explicit `return` statement already emitted the LLVM ret and
                // positioned the builder on a dead block.  LLVM requires every basic
                // block to have a terminator, so emit `unreachable`.
                self.builder
                    .build_unreachable()
                    .map_err(|e| CompileError::ice(e.to_string()))?;
            }
        }

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
        body: &SemExpr,
    ) -> Result<FunctionValue<'ctx>, CompileError> {
        let all_int: Vec<Kind> = vec![Kind::Int; params.len()];
        let function = self.declare_function(name, params, &all_int, Kind::Int);
        self.compile_function_body(function, params, &all_int, body, false, &Env::new())
    }

    /// The bare-scalar-integer Kind a freshly-synthesized value (an integer
    /// literal) should default to in the function currently being compiled —
    /// int-soundness-plan phase 3 step 4b.
    ///
    /// Everything else in the pipeline determines `Kind::Int` vs `Kind::Int64`
    /// by propagating an existing value's Kind (a parameter's declared Kind,
    /// a call's declared return Kind, an arithmetic node's operand Kinds) —
    /// a literal has nothing upstream to inherit from, so it needs this one
    /// piece of ambient context instead. `Kind::Int64` only when the current
    /// function's own declared params/return say so (Step A promotion or a
    /// step 4a `Int64` split arm); `Kind::Int` (tagged) otherwise, including
    /// when there's no current function at all (`compile_function`'s test
    /// convenience wrapper, which always declares plain `Kind::Int`).
    /// `true` only for `compile_constrained`'s pipeline (a real, solver-
    /// verified `ConstrainedTree` — `cantor run`/`cantor check`), reusing
    /// `overflow_ctx` as the existing signal for exactly that distinction
    /// (see its own doc comment). `compile_file`/`compile_items` (the REPL,
    /// `llvm-ir`, and every direct-codegen unit test) never run
    /// `int64_split`'s Step A/4a passes, so nothing there ever produces a
    /// `Kind::Int64` position — tagging `Kind::Int` for BigInt support is
    /// only meaningful, and only safe to turn on, once it might coexist with
    /// a genuine raw `Int64` position. Gating on this (rather than tagging
    /// unconditionally) keeps every one of those unverified-pipeline
    /// consumers on its pre-existing plain-i64 ABI, unchanged.
    pub(crate) fn tagging_active(&self) -> bool {
        self.overflow_ctx.is_some()
    }

    pub(crate) fn current_bare_int_kind(&self) -> Kind {
        let Some(f) = self.current_fn else {
            return Kind::Int;
        };
        let name = f.get_name().to_str().unwrap_or("");
        let is_raw = self.fn_return_kinds.get(name) == Some(&Kind::Int64)
            || self
                .fn_param_kinds
                .get(name)
                .is_some_and(|ks| ks.contains(&Kind::Int64));
        if is_raw { Kind::Int64 } else { Kind::Int }
    }

    /// Borrow the underlying LLVM module (useful for tests and manual IR construction).
    pub fn module(&self) -> &Module<'ctx> {
        &self.module
    }

    pub fn print_ir(&self) {
        self.module.print_to_stderr();
    }
}

/// Evaluate a constant expression at compile time.
fn eval_const(expr: &Expr, known: &HashMap<Symbol, i64>) -> Result<i64, CompileError> {
    match &expr.kind {
        ExprKind::IntLit(n) => Ok(*n),
        ExprKind::Var(sym) => known.get(sym).copied().ok_or_else(|| {
            CompileError::ice(format!(
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
                        Err(CompileError::ice("division by zero in constant expression"))
                    } else {
                        Ok(l / r)
                    }
                }
                _ => Err(CompileError::ice(
                    "only integer arithmetic is supported in constant expressions",
                )),
            }
        }
        _ => Err(CompileError::ice(
            "only integer arithmetic is supported in constant expressions",
        )),
    }
}

/// Compile every function in `items` into a single JIT module.
/// Elaborates `items` up front, then delegates to `compile_elaborated`.
/// Both `compile_file` and `compile_to_ir` use this — they don't require a
/// proof, unlike `compile_constrained`.
pub(super) fn compile_items<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
) -> Result<Compiler<'ctx>, CompileError> {
    let sem_items = elaborate(items)?;
    compile_elaborated(ctx, items, &sem_items, HashMap::new(), None, HashMap::new())
}

/// Compile an already-elaborated file — the shared core of `compile_items`
/// and `compile_constrained`. Does a two-pass compilation (declarations →
/// bodies) into a `Compiler`.
///
/// Takes `items` *and* `sem_items` because pass 0 (constant-folding) below
/// deliberately walks the raw AST rather than the elaborated tree — see its
/// comment for why.
///
/// `overflow_checks`/`overflow_ctx` come from a verified `ConstrainedTree`
/// (`compile_constrained`) or are empty/`None` (`compile_items` — no solver
/// verification ran, so every arithmetic op is conservatively unproved).
/// `overload_resolution` is the same story for int-soundness-plan phase 2:
/// from a verified `ConstrainedTree`, or empty (every overloaded call falls
/// back to runtime dispatch).
pub(super) fn compile_elaborated<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
    sem_items: &[SemItem],
    overflow_checks: HashMap<Span, bool>,
    overflow_ctx: Option<(String, String)>,
    overload_resolution: HashMap<Span, usize>,
) -> Result<Compiler<'ctx>, CompileError> {
    let mut compiler = Compiler::new(ctx, "cantor");
    compiler.overflow_checks = overflow_checks;
    compiler.overflow_ctx = overflow_ctx;
    compiler.overload_resolution = overload_resolution;
    compiler.declare_runtime_functions();

    // Pass 0 — evaluate scalar constants and build a shared env of inlined values.
    // Set-definition NameDefs (e.g. `HTTPError = {400, 503}`) are silently skipped
    // here because they have no scalar value to inline into function bodies; they
    // are collected separately into `user_set_vals` below. This pass works from
    // the raw AST — it's pure constant-folding, not a Kind/position concern the
    // elaborator needs to disambiguate.
    let mut const_vals: HashMap<Symbol, i64> = HashMap::new();
    for item in items {
        if let Item::NameDef(def) = item
            && let Ok(val) = eval_const(&def.value, &const_vals)
        {
            const_vals.insert(def.name.clone(), val);
        }
    }

    // Collect integer-value lists for set-literal NameDefs so that
    // `compile_membership` and `compile_try` can reason about named error sets
    // (e.g. `HTTPError = {400, 503}`) at compile time.
    let mut user_set_vals: HashMap<String, Vec<i64>> = HashMap::new();
    for item in items {
        if let Item::NameDef(def) = item
            && let ExprKind::SetLit(elements) = &def.value.kind
        {
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
    compiler.user_set_vals = user_set_vals;

    compiler.distinct_names = items
        .iter()
        .filter_map(|item| match item {
            Item::NameDef(def) if def.kind == DefKind::Distinct => Some(def.name.0.clone()),
            _ => None,
        })
        .collect();

    // int-soundness-plan phase 3 step 4b: a named scalar constant is always
    // genuinely `Kind::Int` (tagged) — it's inlined unchanged into every
    // function's env regardless of that function's own representation, so
    // it can't default to `Int64` the way a bare literal inside a
    // Step-A-promoted body can (`current_bare_int_kind`). Whatever consumes
    // it (arithmetic, a call boundary) already knows how to reconcile a
    // tagged value against a raw one.
    let mut const_env: Env<'ctx> = Env::new();
    for (sym, &val) in &const_vals {
        let llvm_val = compiler.compile_tagged_i64_const(val)?;
        const_env.insert(sym.clone(), (llvm_val.into(), Kind::Int));
    }

    // int-soundness-plan phase 2: how many `FunctionDef`s share each name —
    // a count of 1 (the overwhelming common case) keeps today's plain LLVM
    // name; more than 1 is an overload set, mangled below so `add_function`
    // is never called twice under the same name (LLVM would otherwise
    // silently rename the second and nothing would ever call it).
    let mut overload_counts: HashMap<Symbol, usize> = HashMap::new();
    for item in sem_items {
        if let SemItem::FunctionDef(def) = item {
            *overload_counts.entry(def.name.clone()).or_insert(0) += 1;
        }
    }

    // Pass 1 — declare all function signatures so forward calls resolve.
    // Param and return Kinds come from the elaborator's first-signature
    // computation; overloaded functions must agree on the Kind of each
    // position within a (name, arity) group (enforced during elaboration).
    let mut next_overload_index: HashMap<Symbol, usize> = HashMap::new();
    let decls: Vec<(FunctionValue<'ctx>, &crate::semantics::tree::SemFunctionDef)> = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::FunctionDef(def) => {
                let is_overloaded = overload_counts[&def.name] > 1;
                let index = next_overload_index.entry(def.name.clone()).or_insert(0);
                let overload_index = *index;
                *index += 1;

                let llvm_name = if is_overloaded {
                    format!("{}__ov{overload_index}", def.name.0)
                } else {
                    def.name.0.clone()
                };

                let fn_val = compiler.declare_function(
                    &llvm_name,
                    &def.params,
                    &def.param_kinds,
                    def.return_kind.clone(),
                );
                // Record the range expression so `compile_try` can determine what
                // error values `?` should propagate for this callee.
                if let Some(sig) = def.sigs.first() {
                    compiler
                        .fn_ranges
                        .insert(llvm_name.clone(), sig.range.clone());
                    // Record per-parameter domain set expressions so `coerce_call_arg`
                    // can disambiguate which arm of a `+`-typed parameter a scalar
                    // call argument belongs to.
                    if let Ok(parts) = crate::semantics::tree::sem_param_set_exprs(
                        sig.domain.as_ref(),
                        def.params.len(),
                    ) {
                        let parts: Vec<SemExpr> = parts.into_iter().cloned().collect();
                        if is_overloaded {
                            compiler
                                .overload_dispatch
                                .entry(def.name.0.clone())
                                .or_default()
                                .push(OverloadEntry {
                                    mangled_name: llvm_name.clone(),
                                    arity: def.params.len(),
                                    domain_parts: parts.clone(),
                                });
                        }
                        compiler.fn_param_set_exprs.insert(llvm_name.clone(), parts);
                    } else if is_overloaded {
                        // Domain didn't decompose (arity mismatch shouldn't
                        // happen here since this is the def's own params
                        // count) — still register the candidate so dispatch
                        // knows about it, with an empty (always-Trivial)
                        // domain-parts list rather than dropping it silently.
                        compiler
                            .overload_dispatch
                            .entry(def.name.0.clone())
                            .or_default()
                            .push(OverloadEntry {
                                mangled_name: llvm_name.clone(),
                                arity: def.params.len(),
                                domain_parts: Vec::new(),
                            });
                    }
                }
                Some((fn_val, def))
            }
            // Compile-time-only proof obligation (like `require`) — no
            // codegen, no runtime representation, nothing to declare.
            SemItem::NameDef(_) | SemItem::EquivDecl { .. } => None,
        })
        .collect();

    // Pass 2 — compile bodies with constants available.
    for (fn_val, def) in decls {
        let is_fallible = def
            .sigs
            .iter()
            .any(|s| crate::semantics::tree::range_contains_fail(&s.range));

        match &def.body {
            SemFunctionBody::Expr(e) => {
                compiler.compile_function_body(
                    fn_val,
                    &def.params,
                    &def.param_kinds,
                    e,
                    is_fallible,
                    &const_env,
                )?;
            }
            SemFunctionBody::Block(stmts) => {
                compiler.compile_block_body(
                    fn_val,
                    &def.params,
                    &def.param_kinds,
                    stmts,
                    is_fallible,
                    &const_env,
                )?;
            }
        }
    }

    // Emit trampolines for `main` depending on its return kind.
    if let Some(main_fn) = compiler.module.get_function("main") {
        let ret_kind = compiler
            .fn_return_kinds
            .get("main")
            .cloned()
            .unwrap_or(Kind::Int);
        match &ret_kind {
            // Fallible main: emit an i64-returning runner that converts {i1, i64} to flat i64.
            Kind::Tuple(elems) if elems.first() == Some(&Kind::Fail) => {
                compiler.emit_fallible_main_runner(main_fn)?;
            }
            // Regular tuple main: emit the existing ptr-buffer trampoline.
            Kind::Tuple(_) => {
                compiler.emit_tuple_main_trampoline(main_fn, &ret_kind)?;
            }
            _ => {}
        }
    }

    Ok(compiler)
}

/// Compile a parsed file and return the LLVM IR as a string (no JIT).
///
/// Useful in tests to assert whether something was handled at compile time
/// (no runtime calls in the IR) or at runtime (runtime calls present).
pub fn compile_to_ir(ctx: &Context, items: &[Item]) -> Result<String, CompileError> {
    let compiler = compile_items(ctx, items)?;
    Ok(compiler.module().print_to_string().to_string())
}
