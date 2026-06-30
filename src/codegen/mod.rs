use std::collections::{HashMap, HashSet};

use inkwell::{
    AddressSpace,
    IntPredicate,
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{AggregateValueEnum, BasicValueEnum, FunctionValue},
};

use crate::{
    ast::{
        BinOp, DefKind, Expr, ExprKind, FunctionBody, FunctionDef, Item, NameDefs, Param, Stmt,
        UnOp, flatten_disjoint_union, param_set_exprs,
    },
    error::CompileError,
    kind::Kind,
    span::Symbol,
};

mod blocks;
mod expr;
mod expr_vec;
mod jit;
mod loops;
mod membership;
pub mod wire;

use wire::{param_kinds, range_kind, tagged_union_leaf_count};

pub use jit::compile_file;

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
    fn_ranges: HashMap<String, Expr>,
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
    fn_param_set_exprs: HashMap<String, Vec<Expr>>,
    /// All user-defined named set definitions in the file, used to resolve
    /// aliases and distinct sets in `set_kind` calls during codegen.
    pub(crate) name_defs: NameDefs,
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
            name_defs: NameDefs::new(),
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
            param_kinds.iter().map(|k| match k {
                Kind::Tuple(_) | Kind::TaggedUnion(_) => self.kind_to_llvm_type(k).into(),
                _ => i64_type.into(),
            }).collect()
        };
        let fn_val = match &return_kind {
            Kind::Tuple(_) | Kind::TaggedUnion(_) => {
                let ret_type = self.kind_to_llvm_type(&return_kind);
                self.module.add_function(name, ret_type.fn_type(&param_types, false), None)
            }
            _ => {
                self.module.add_function(name, i64_type.fn_type(&param_types, false), None)
            }
        };
        self.fn_return_kinds.insert(name.to_owned(), return_kind);
        self.fn_param_kinds.insert(name.to_owned(), param_kinds.to_vec());
        fn_val
    }

    /// Map a Kind to the natural LLVM type used inside structs and as tuple ABI types.
    /// Scalars: Int/Set/Union → i64, Bool → i1.  Tuple → struct of element types.
    /// TaggedUnion → `{ i32 tag, i64, …, i64 }` with enough i64 slots for the widest arm.
    pub(crate) fn kind_to_llvm_type(&self, kind: &Kind) -> BasicTypeEnum<'ctx> {
        match kind {
            Kind::Int | Kind::Set(_) => self.context.i64_type().into(),
            Kind::Bool | Kind::Fail => self.context.bool_type().into(),
            Kind::Tuple(elems) => {
                let types: Vec<BasicTypeEnum<'ctx>> = elems.iter()
                    .map(|k| self.kind_to_llvm_type(k))
                    .collect();
                self.context.struct_type(&types, false).into()
            }
            Kind::TaggedUnion(arms) => {
                let n = tagged_union_leaf_count(arms);
                let i32t: BasicTypeEnum = self.context.i32_type().into();
                let i64t: BasicTypeEnum = self.context.i64_type().into();
                let mut fields = vec![i32t];
                fields.extend(std::iter::repeat(i64t).take(n));
                self.context.struct_type(&fields, false).into()
            }
            // Vector is an i64 pointer-as-i64 (same wire type as Set).
            Kind::Vector(_) => self.context.i64_type().into(),
        }
    }

    /// Returns the `{i1, i64}` struct type used for all fallible function returns.
    pub(crate) fn fail_struct_type(&self) -> inkwell::types::StructType<'ctx> {
        self.context.struct_type(&[
            self.context.bool_type().into(),
            self.context.i64_type().into(),
        ], false)
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
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());
        match arm_kind {
            Kind::Int | Kind::Set(_) => {
                *agg = self.builder
                    .build_insert_value(*agg, val.into_int_value(), *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
            Kind::Bool | Kind::Fail => {
                let wide = self.builder
                    .build_int_z_extend(val.into_int_value(), i64t, "tu_lb")
                    .map_err(err)?;
                *agg = self.builder
                    .build_insert_value(*agg, wide, *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
            Kind::Tuple(elems) => {
                let sv = AggregateValueEnum::StructValue(val.into_struct_value());
                for (i, ek) in elems.iter().enumerate() {
                    let elem = self.builder
                        .build_extract_value(sv, i as u32, "tu_te")
                        .map_err(err)?;
                    self.insert_kind_leaves(agg, elem, ek, field_idx)?;
                }
            }
            Kind::TaggedUnion(_) => {
                return Err(CompileError::Internal(
                    "insert_kind_leaves: nested TaggedUnion not yet supported".into(),
                ));
            }
            // Vector is an i64 pointer — insert it like Int/Set.
            Kind::Vector(_) => {
                *agg = self.builder
                    .build_insert_value(*agg, val.into_int_value(), *field_idx, "tu_l")
                    .map_err(err)?;
                *field_idx += 1;
            }
        }
        Ok(())
    }

    /// Pack `arm_value : arm_kind` into the `{ i32 tag, i64… }` tagged-union struct
    /// for `Kind::TaggedUnion(all_arms)`, placing the tag at field 0 and the
    /// serialised leaves in fields 1..N.
    pub(crate) fn build_tagged_union_value(
        &self,
        arm_idx: usize,
        arm_value: BasicValueEnum<'ctx>,
        arm_kind: &Kind,
        all_arms: &[Kind],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let tag = self.context.i32_type().const_int(arm_idx as u64, false);
        self.build_tagged_union_value_with_tag(tag, arm_value, arm_kind, all_arms)
    }

    /// Same as [`Self::build_tagged_union_value`] but takes a runtime-computed
    /// tag instead of a compile-time-constant arm index — used when the arm
    /// can only be determined by a runtime membership check (see
    /// `select_disjoint_union_arm`).
    pub(crate) fn build_tagged_union_value_with_tag(
        &self,
        tag: inkwell::values::IntValue<'ctx>,
        arm_value: BasicValueEnum<'ctx>,
        arm_kind: &Kind,
        all_arms: &[Kind],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let struct_ty = self.kind_to_llvm_type(&Kind::TaggedUnion(all_arms.to_vec()))
            .into_struct_type();
        let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
        agg = self.builder
            .build_insert_value(agg, tag, 0, "tu_tag")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let mut field_idx = 1u32;
        self.insert_kind_leaves(&mut agg, arm_value, arm_kind, &mut field_idx)?;
        Ok(agg.into_struct_value().into())
    }

    /// Low-level: copy the leaf i64 fields from a TaggedUnion struct into a
    /// (possibly wider) merged struct, using `new_tag` as the tag field.
    ///
    /// Extra i64 leaf fields beyond `old_leaf_count` are left undef — safe because
    /// they are only ever read via the arm that originally wrote them.
    fn rewrap_tagged_union_with_tag(
        &self,
        val: BasicValueEnum<'ctx>,
        old_arms: &[Kind],
        new_arms: &[Kind],
        new_tag: inkwell::values::IntValue<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let old_leaf_count = tagged_union_leaf_count(old_arms);
        let new_struct_ty = self.kind_to_llvm_type(&Kind::TaggedUnion(new_arms.to_vec()))
            .into_struct_type();
        let old_struct = AggregateValueEnum::StructValue(val.into_struct_value());
        let mut agg: AggregateValueEnum<'ctx> = new_struct_ty.get_undef().into();
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());
        agg = self.builder.build_insert_value(agg, new_tag, 0, "tu_rw_t").map_err(err)?;
        for i in 0..old_leaf_count {
            let leaf = self.builder
                .build_extract_value(old_struct, (i + 1) as u32, "tu_rw_l")
                .map_err(err)?;
            agg = self.builder
                .build_insert_value(agg, leaf, (i + 1) as u32, "tu_rw_li")
                .map_err(err)?;
        }
        Ok(agg.into_struct_value().into())
    }

    /// Extend a `TaggedUnion(old_arms)` value into a wider `TaggedUnion(new_arms)` struct.
    ///
    /// `old_arms` must be a prefix of `new_arms` (arm indices are preserved).
    pub(crate) fn rewrap_tagged_union_value(
        &self,
        val: BasicValueEnum<'ctx>,
        old_arms: &[Kind],
        new_arms: &[Kind],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let old_struct = AggregateValueEnum::StructValue(val.into_struct_value());
        let tag = self.builder
            .build_extract_value(old_struct, 0, "tu_rw_tag")
            .map_err(|e| CompileError::Internal(e.to_string()))?
            .into_int_value();
        self.rewrap_tagged_union_with_tag(val, old_arms, new_arms, tag)
    }

    /// Remap an i32 tag value using `mapping[old_arm_idx] = new_arm_idx`.
    ///
    /// Emits a chain of LLVM `select` instructions that evaluate at runtime.
    pub(crate) fn remap_tagged_union_tag(
        &self,
        old_tag: inkwell::values::IntValue<'ctx>,
        mapping: &[usize],
    ) -> Result<inkwell::values::IntValue<'ctx>, CompileError> {
        let i32t = self.context.i32_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());
        // Default: the last arm's new index (used when no earlier select fires).
        let mut current = i32t.const_int(*mapping.last().unwrap() as u64, false);
        // Build selects in reverse order so the chain evaluates correctly.
        for (old_idx, &new_idx) in mapping[..mapping.len() - 1].iter().enumerate().rev() {
            let is_this = self.builder
                .build_int_compare(
                    IntPredicate::EQ,
                    old_tag,
                    i32t.const_int(old_idx as u64, false),
                    "tu_tag_eq",
                )
                .map_err(err)?;
            current = self.builder
                .build_select(
                    is_this,
                    i32t.const_int(new_idx as u64, false),
                    current,
                    "tu_tag_sel",
                )
                .map_err(err)?
                .into_int_value();
        }
        Ok(current)
    }

    /// If the function's declared return kind is `Kind::Vector(elem)` but the compiled
    /// value is `Kind::Tuple(elems)` (from an array literal like `[1, 2, 3]`), coerce
    /// by building an Arrow vector from the tuple's elements at runtime.
    ///
    /// Returns `(val, kind)` unchanged when no coercion is needed.
    pub(crate) fn coerce_vector_return(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: Kind,
        function: FunctionValue<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let fn_name = function.get_name().to_str().unwrap_or("");
        let expected = self.fn_return_kinds.get(fn_name).cloned().unwrap_or_else(|| val_kind.clone());
        let elem_kind = match &expected {
            Kind::Vector(ek) => ek.as_ref().clone(),
            _ => return Ok((val, val_kind)),
        };
        match &val_kind {
            Kind::Vector(_) => Ok((val, val_kind)), // already a vector
            Kind::Tuple(elems) => {
                let elems = elems.clone();
                self.compile_tuple_as_vector(val, &elems, &elem_kind)
            }
            Kind::Int | Kind::Bool => self.compile_scalar_as_singleton_vector(val, &val_kind, &elem_kind),
            other => Err(CompileError::Internal(format!(
                "coerce_vector_return: cannot convert {other:?} to Vector"
            ))),
        }
    }

    /// If the function's declared return kind is `Kind::TaggedUnion(arms)` and
    /// `val_kind` is not already that union, find the matching arm and wrap.
    /// Conversely, if `val_kind` is a `TaggedUnion` but the declared return is
    /// a plain scalar, narrow it back down by dropping the tag — needed when
    /// a `+`-typed (forced-disjoint) value is returned into a non-disjoint
    /// context, e.g. `{0} + NatPos -> Nat; main(x) = x`.
    /// Returns `(val, kind)` — unchanged if no coercion is needed.
    pub(crate) fn coerce_tagged_union_return(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: Kind,
        function: FunctionValue<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let fn_name = function.get_name().to_str().unwrap_or("");
        let expected = self.fn_return_kinds.get(fn_name).cloned().unwrap_or_else(|| val_kind.clone());
        let set_expr = self.fn_ranges.get(fn_name);
        self.coerce_to_kind(val, val_kind, &expected, set_expr)
    }

    /// Coerce a call argument `val : val_kind` to the callee's `expected`
    /// param Kind — the call-site mirror of `coerce_tagged_union_return`.
    /// Needed when a scalar value is passed directly into a `+`-typed
    /// (forced-disjoint) parameter, e.g. `accept_nat(7)` where
    /// `accept_nat : {0} + NatPos -> Nat`.
    pub(crate) fn coerce_call_arg(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: Kind,
        expected: &Kind,
        callee: &str,
        arg_idx: usize,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let set_expr = self.fn_param_set_exprs.get(callee).and_then(|exprs| exprs.get(arg_idx));
        self.coerce_to_kind(val, val_kind, expected, set_expr)
    }

    /// Shared core for `coerce_tagged_union_return` and `coerce_call_arg`:
    /// coerce `val : val_kind` to `expected`, widening a scalar/tuple into a
    /// declared TaggedUnion, or narrowing a TaggedUnion back to a declared
    /// scalar. `set_expr` (the range/domain expression `expected` was derived
    /// from) is only consulted when multiple TaggedUnion arms share
    /// `val_kind` and must be runtime-disambiguated via a membership check —
    /// only possible for `+`, which keeps same-kind arms distinct on purpose.
    fn coerce_to_kind(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: Kind,
        expected: &Kind,
        set_expr: Option<&Expr>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let arms = match expected {
            Kind::TaggedUnion(a) => a.clone(),
            _ => {
                return match &val_kind {
                    Kind::TaggedUnion(val_arms) => self.narrow_tagged_union(val, val_arms, expected),
                    _ => Ok((val, val_kind)),
                };
            }
        };
        if matches!(&val_kind, Kind::TaggedUnion(a) if a == &arms) {
            return Ok((val, val_kind)); // already the right TaggedUnion
        }
        let candidates: Vec<usize> = arms.iter().enumerate()
            .filter(|(_, k)| **k == val_kind)
            .map(|(i, _)| i)
            .collect();
        match candidates.as_slice() {
            [] => Err(CompileError::Internal(format!(
                "coerce_to_kind: value kind {val_kind:?} does not match any arm of {arms:?}"
            ))),
            [arm_idx] => {
                let wrapped = self.build_tagged_union_value(*arm_idx, val, &val_kind, &arms)?;
                Ok((wrapped, expected.clone()))
            }
            _ => {
                let set_expr = set_expr.ok_or_else(|| CompileError::Internal(format!(
                    "coerce_to_kind: value kind {val_kind:?} matches multiple arms of {arms:?} \
                     but no set expression was recorded to disambiguate them"
                )))?;
                let wrapped = self.select_disjoint_union_arm(val, &val_kind, &arms, &candidates, set_expr)?;
                Ok((wrapped, expected.clone()))
            }
        }
    }

    /// Coerce `val : kind` down to a raw scalar `IntValue`, narrowing a
    /// `TaggedUnion` (e.g. a `+`-typed value) by dropping its tag first.
    ///
    /// Used wherever an expression is consumed as a plain integer — arithmetic,
    /// comparisons, etc. — so a `+`-typed variable like `x : {0} + NatPos` can
    /// be used directly in `x + 1`. Only single-leaf-scalar arms are supported
    /// today (see `narrow_tagged_union`); anything else fails loudly rather
    /// than panicking on a mismatched `into_int_value()`.
    pub(crate) fn scalarize_to_int(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
    ) -> Result<inkwell::values::IntValue<'ctx>, CompileError> {
        match kind {
            Kind::TaggedUnion(arms) => {
                let (narrowed, _) = self.narrow_tagged_union(val, arms, &Kind::Int)?;
                Ok(narrowed.into_int_value())
            }
            _ => Ok(val.into_int_value()),
        }
    }

    /// Narrow a `TaggedUnion(arms)` value down to a plain scalar `expected`
    /// Kind by dropping the tag and reading the single i64 payload field.
    /// Valid only when every arm is a single-leaf scalar (Int/Bool) — e.g.
    /// unwrapping a `+`-typed value (forced-disjoint, same payload shape per
    /// arm) back into a non-disjoint context.
    fn narrow_tagged_union(
        &self,
        val: BasicValueEnum<'ctx>,
        val_arms: &[Kind],
        expected: &Kind,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let supported = matches!(expected, Kind::Int | Kind::Bool)
            && val_arms.iter().all(|k| matches!(k, Kind::Int | Kind::Bool));
        if !supported {
            return Err(CompileError::Internal(format!(
                "narrow_tagged_union: not yet implemented for arms {val_arms:?} -> {expected:?}"
            )));
        }
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());
        let payload = self.builder
            .build_extract_value(val.into_struct_value(), 1, "tu_narrow_payload")
            .map_err(err)?
            .into_int_value();
        let result: BasicValueEnum = if matches!(expected, Kind::Bool) {
            self.builder
                .build_int_truncate(payload, self.context.bool_type(), "tu_narrow_bool")
                .map_err(err)?
                .into()
        } else {
            payload.into()
        };
        Ok((result, expected.clone()))
    }

    /// Resolve which arm of a `+`-typed (forced-disjoint) return a scalar
    /// value belongs to when multiple arms share the same elaborated Kind
    /// (e.g. `{0}` and `NatPos` are both `Kind::Int`). Builds a runtime
    /// membership check against each candidate arm's named set, in
    /// declaration order, defaulting to the last candidate — the function's
    /// domain is solver-checked, so by construction the value belongs to
    /// exactly one of them.
    fn select_disjoint_union_arm(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: &Kind,
        arms: &[Kind],
        candidates: &[usize],
        set_expr: &Expr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let arm_exprs = flatten_disjoint_union(set_expr);
        if arm_exprs.len() != arms.len() {
            return Err(CompileError::Internal(format!(
                "select_disjoint_union_arm: not yet implemented for a Kind whose TaggedUnion \
                 arms ({}) don't align with a top-level `+` chain in the recorded set \
                 expression ({} parts) — only plain `A + B + …` domains/ranges are supported today",
                arms.len(), arm_exprs.len()
            )));
        }

        let i32t = self.context.i32_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());
        let val_int = val.into_int_value();

        let (&last, rest) = candidates.split_last().ok_or_else(|| CompileError::Internal(
            "select_disjoint_union_arm: called with no candidate arms".into()
        ))?;
        let mut tag = i32t.const_int(last as u64, false);
        for &candidate in rest.iter().rev() {
            let in_arm = self.compile_membership(val_int, arm_exprs[candidate])?;
            let candidate_tag = i32t.const_int(candidate as u64, false);
            tag = self.builder
                .build_select(in_arm, candidate_tag, tag, "tu_arm_sel")
                .map_err(err)?
                .into_int_value();
        }

        self.build_tagged_union_value_with_tag(tag, val, val_kind, arms)
    }

    /// Build a `{i1=0, i64=payload}` success-tagged struct.
    pub(crate) fn build_success_struct(
        &self,
        payload: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let zero_i1 = self.context.bool_type().const_int(0, false);
        let s = self.fail_struct_type().get_undef();
        let s = self.builder
            .build_insert_value(s, zero_i1, 0, "sv_flag")
            .map_err(|e| CompileError::Internal(e.to_string()))?
            .into_struct_value();
        let s = self.builder
            .build_insert_value(s, payload, 1, "sv_payload")
            .map_err(|e| CompileError::Internal(e.to_string()))?
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
        let s = self.builder
            .build_insert_value(s, one_i1, 0, "fv_flag")
            .map_err(|e| CompileError::Internal(e.to_string()))?
            .into_struct_value();
        let s = self.builder
            .build_insert_value(s, payload, 1, "fv_payload")
            .map_err(|e| CompileError::Internal(e.to_string()))?
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
        let i64t = self.context.i64_type();
        let payload = match kind {
            Kind::Bool => self.builder
                .build_int_z_extend(val.into_int_value(), i64t, "coerce_bool")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into(),
            Kind::Int => val,
            _ => return Err(CompileError::Internal(
                "cannot coerce value to fail struct: unsupported kind".into(),
            )),
        };
        self.build_success_struct(payload)
    }

    /// Wrap a return value for a fallible function if needed.
    ///
    /// - Already a fail struct → pass through (e.g. from `FailLit`, `compile_try`)
    /// - Bool in non-fallible function → zero-extend to i64
    /// - Any other value in non-fallible function → pass through
    /// - Any non-struct value in fallible function → wrap in `{i1=0, i64=val}`
    pub(crate) fn wrap_return_value(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        if self.fail_bb.is_none() {
            // Non-fallible: apply Bool-to-i64 extension and pass through.
            return Ok(if *kind == Kind::Bool {
                self.builder
                    .build_int_z_extend(val.into_int_value(), self.context.i64_type(), "bool_ret")
                    .map_err(|e| CompileError::Internal(e.to_string()))?
                    .into()
            } else {
                val
            });
        }
        // Fallible function: ensure the value is a {i1, i64} struct.
        if matches!(kind, Kind::Tuple(e) if e.first() == Some(&Kind::Fail)) {
            return Ok(val); // already a fail struct
        }
        let i64t = self.context.i64_type();
        let payload = match kind {
            Kind::Bool => self.builder
                .build_int_z_extend(val.into_int_value(), i64t, "bool_ret")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into(),
            _ => val,
        };
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
        body: &Expr,
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
            } else if matches!(kind, Kind::Tuple(_) | Kind::TaggedUnion(_)) {
                (llvm_param, kind.clone())
            } else if matches!(kind, Kind::Vector(_) | Kind::Set(_)) {
                (llvm_param, kind.clone())
            } else {
                (llvm_param, Kind::Int)
            };
            env.insert(param.name.clone(), entry);
        }

        let (val, ty) = self.compile_expr(body, &env)?;
        let (val, ty) = self.coerce_vector_return(val, ty, function)?;
        let (val, ty) = self.coerce_tagged_union_return(val, ty, function)?;
        let ret_val = self.wrap_return_value(val, &ty)?;

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
            // Bare assert failure returns {i1=1, i64=0} — no typed error code.
            let fail_struct = self.fail_struct_type().const_named_struct(&[
                self.context.bool_type().const_int(1, false).into(),
                self.context.i64_type().const_int(0, false).into(),
            ]);
            self.builder
                .build_return(Some(&BasicValueEnum::StructValue(fail_struct)))
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
            } else if matches!(kind, Kind::Tuple(_) | Kind::TaggedUnion(_)) {
                (llvm_param, kind.clone())
            } else if matches!(kind, Kind::Vector(_) | Kind::Set(_)) {
                (llvm_param, kind.clone())
            } else {
                (llvm_param, Kind::Int)
            };
            env.insert(param.name.clone(), entry);
        }

        let return_val = self.compile_stmts(stmts, &mut env, &HashMap::new())?;

        match return_val {
            Some((val, kind)) => {
                let (val, kind) = self.coerce_vector_return(val, kind, function)?;
                let (val, kind) = self.coerce_tagged_union_return(val, kind, function)?;
                let ret_val = self.wrap_return_value(val, &kind)?;
                self.builder
                    .build_return(Some(&ret_val))
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
            }
            None => {
                // An explicit `return` statement already emitted the LLVM ret and
                // positioned the builder on a dead block.  LLVM requires every basic
                // block to have a terminator, so emit `unreachable`.
                self.builder
                    .build_unreachable()
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
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
    /// `into_jit_engine` (in `jit.rs`) registers the actual function pointers
    /// so the JIT can resolve the calls.
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

        // Vector(Int) ABI — Apache Arrow Int64Array, pointer-as-i64.
        self.module.add_function("cantor_vec_builder_new_i64",    i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_vec_builder_push_i64",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_builder_finish_i64", i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_len_i64",            i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_get_i64",            i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_push_i64",           i64t.fn_type(ii,   false), None);

        // Vector(Bool) ABI — Apache Arrow BooleanArray, pointer-as-i64.
        // Booleans passed as i64 (0/1) matching the uniform ABI.
        self.module.add_function("cantor_vec_builder_new_bool",    i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_vec_builder_push_bool",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_builder_finish_bool", i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_len_bool",            i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_get_bool",            i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_push_bool",           i64t.fn_type(ii,   false), None);

        // Concatenation — both take two i64 pointers and return a new i64 pointer.
        self.module.add_function("cantor_vec_concat_i64",          i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_concat_bool",         i64t.fn_type(ii,   false), None);

        // Nested vector (X** at any depth) — generic CantorListVec (Int64Array of opaque i64 ptrs).
        // All functions are suffix-free: the codegen never needs to know the Arrow child type.
        self.module.add_function("cantor_list_vec_builder_new",    i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_list_vec_builder_push",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_list_vec_builder_finish", i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_list_vec_len",            i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_list_vec_get",            i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_list_vec_concat",         i64t.fn_type(ii,   false), None);

        // Struct vectors ((A * B)*) — backed by Arrow StructArray; all field values stored as i64.
        // push_field / get_field take (ptr, field_idx, value) — three i64 args.
        let iii = &[i64t.into(), i64t.into(), i64t.into()] as &[_];
        self.module.add_function("cantor_struct_vec_builder_new",        i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_struct_vec_builder_push_field", void.fn_type(iii,  false), None);
        self.module.add_function("cantor_struct_vec_builder_finish",     i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_struct_vec_len",                i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_struct_vec_get_field",          i64t.fn_type(iii,  false), None);
        self.module.add_function("cantor_struct_vec_concat",             i64t.fn_type(ii,   false), None);

        // Union vectors (Kind::Vector(Kind::TaggedUnion(arms))) — DenseUnionArray,
        // one StructArray child per arm (each with leaf_count(arm) Int64Array columns).
        // set_arm takes (builder, arm_idx, n_leaves) — three i64 args.
        // push_leaf takes (builder, arm_idx, leaf_idx, value) — four i64 args.
        // get_leaf takes (vec, row_idx, leaf_idx) — three i64 args.
        let iiii = &[i64t.into(), i64t.into(), i64t.into(), i64t.into()] as &[_];
        self.module.add_function("cantor_union_vec_builder_new",       i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_union_vec_builder_set_arm",   void.fn_type(iii,  false), None);
        self.module.add_function("cantor_union_vec_builder_push_leaf", void.fn_type(iiii, false), None);
        self.module.add_function("cantor_union_vec_builder_finish",    i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_union_vec_len",               i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_union_vec_get_tag",           i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_union_vec_get_leaf",          i64t.fn_type(iii,  false), None);
        self.module.add_function("cantor_union_vec_concat",            i64t.fn_type(ii,   false), None);
    }

    pub fn print_ir(&self) {
        self.module.print_to_stderr();
    }
}

/// True if the range expression can produce a failure value at runtime.
///
/// Covers `| Fail`, `| (Fail * Y)` (desugared from `!! Y`), and their unions.
pub fn range_contains_fail(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::Var(sym) => sym.0 == "Fail",
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            range_contains_fail(lhs) || range_contains_fail(rhs)
        }
        // `Fail * Y` — desugared from `!! Y`; always a failure arm.
        ExprKind::BinOp { op: BinOp::Mul, lhs, .. } => {
            matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
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
/// Three-pass compilation (constants → declarations → bodies) into a `Compiler`.
/// Both `compile_file` and `compile_to_ir` delegate here.
pub(super) fn compile_items<'ctx>(
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

    compiler.name_defs = items
        .iter()
        .filter_map(|item| match item {
            Item::NameDef(def) => Some((def.name.clone(), def.clone())),
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
                    .map(|s| param_kinds(s, def.params.len(), &compiler.name_defs))
                    .unwrap_or_else(|| vec![Kind::Int; def.params.len()]);
                let ret_kind = first_sig
                    .map(|s| range_kind(&s.range, &compiler.name_defs))
                    .unwrap_or(Kind::Int);
                let fn_val = compiler.declare_function(&def.name.0, &def.params, &p_kinds, ret_kind);
                // Record the range expression so `compile_try` can determine what
                // error values `?` should propagate for this callee.
                if let Some(sig) = first_sig {
                    compiler.fn_ranges.insert(def.name.0.clone(), sig.range.clone());
                    // Record per-parameter domain set expressions so `coerce_call_arg`
                    // can disambiguate which arm of a `+`-typed parameter a scalar
                    // call argument belongs to.
                    if let Ok(parts) = param_set_exprs(sig.domain.as_ref(), def.params.len()) {
                        compiler.fn_param_set_exprs.insert(
                            def.name.0.clone(),
                            parts.into_iter().cloned().collect(),
                        );
                    }
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
            .map(|s| param_kinds(s, def.params.len(), &compiler.name_defs))
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

    // Emit trampolines for `main` depending on its return kind.
    if let Some(main_fn) = compiler.module.get_function("main") {
        let ret_kind = compiler.fn_return_kinds.get("main").cloned().unwrap_or(Kind::Int);
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

impl<'ctx> Compiler<'ctx> {
    /// Emit `i64 @__cantor_main_runner()` for fallible `main`.
    ///
    /// Calls `main()` which returns `{i1, i64}`, then:
    ///  - Success (flag=0): returns the i64 payload directly.
    ///  - Failure (flag=1): stores the error code to `@__cantor_fail_code`, returns
    ///    `JIT_RUNNER_SENTINEL` so the Rust caller can detect failure.
    ///
    /// `@__cantor_fail_code` (global i64) can be read by Rust after the call via
    /// `get_global_value_address` to surface a typed error code to the user.
    ///
    /// The sentinel is only used at the thin JIT boundary; all internal codegen
    /// uses `{i1, i64}` structs directly.
    fn emit_fallible_main_runner(
        &self,
        main_fn: FunctionValue<'ctx>,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();

        // Global that the runner fills with the error code on failure.
        let fail_code_global = self.module.add_global(i64t, None, "__cantor_fail_code");
        fail_code_global.set_initializer(&i64t.const_int(0, false));

        let runner = self.module.add_function(
            "__cantor_main_runner",
            i64t.fn_type(&[], false),
            None,
        );

        let entry_bb = self.context.append_basic_block(runner, "entry");
        let fail_bb  = self.context.append_basic_block(runner, "fail");
        let ok_bb    = self.context.append_basic_block(runner, "ok");

        let err = |e: inkwell::builder::BuilderError| CompileError::Internal(e.to_string());

        self.builder.position_at_end(entry_bb);
        let call = self.builder
            .build_call(main_fn, &[], "main_result")
            .map_err(err)?;
        let struct_val = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Internal("main returned void in runner".into()))?
            .into_struct_value();
        let flag = self.builder
            .build_extract_value(struct_val, 0, "runner_flag")
            .map_err(err)?
            .into_int_value();
        self.builder.build_conditional_branch(flag, fail_bb, ok_bb).map_err(err)?;

        self.builder.position_at_end(fail_bb);
        let error_code = self.builder
            .build_extract_value(struct_val, 1, "runner_err_code")
            .map_err(err)?;
        let fail_code_ptr = fail_code_global.as_pointer_value();
        self.builder
            .build_store(fail_code_ptr, error_code)
            .map_err(err)?;
        let sentinel = i64t.const_int(JIT_RUNNER_SENTINEL as u64, true);
        self.builder.build_return(Some(&sentinel)).map_err(err)?;

        self.builder.position_at_end(ok_bb);
        let payload = self.builder
            .build_extract_value(struct_val, 1, "runner_payload")
            .map_err(err)?;
        self.builder.build_return(Some(&payload)).map_err(err)?;

        // Emit a getter so Rust can read the error code via JIT without needing
        // inkwell's (missing) `get_global_value_address` API.
        let getter = self.module.add_function(
            "__cantor_get_fail_code",
            i64t.fn_type(&[], false),
            None,
        );
        let getter_bb = self.context.append_basic_block(getter, "entry");
        self.builder.position_at_end(getter_bb);
        let loaded = self.builder
            .build_load(i64t, fail_code_global.as_pointer_value(), "fail_code")
            .map_err(err)?;
        self.builder.build_return(Some(&loaded)).map_err(err)?;

        Ok(())
    }

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
            Kind::Bool | Kind::Fail => {
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
            // TODO: tagged-union IR — emit the raw struct fields for now;
            // a proper trampoline would inspect the tag and decode each arm.
            Kind::TaggedUnion(_) => {
                return Err(CompileError::Internal(
                    "trampoline_store_leaves: TaggedUnion output not yet supported".into(),
                ));
            }
            // Vector is an i64 pointer — store it like any other i64 leaf.
            Kind::Vector(_) => {
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    unsafe { builder.build_gep(i64t, out_ptr, &[idx], "gp").map_err(err)? }
                };
                builder.build_store(ptr, val.into_int_value()).map_err(err)?;
                *leaf_idx += 1;
            }
        }
        Ok(())
    }
}

/// Compile a parsed file and return the LLVM IR as a string (no JIT).
///
/// Useful in tests to assert whether something was handled at compile time
/// (no runtime calls in the IR) or at runtime (runtime calls present).
pub fn compile_to_ir<'ctx>(ctx: &'ctx Context, items: &[Item]) -> Result<String, CompileError> {
    let compiler = compile_items(ctx, items)?;
    Ok(compiler.module().print_to_string().to_string())
}
