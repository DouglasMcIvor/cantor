//! TaggedUnion construction and coercion.
//!
//! Building `{ i32 tag, i64… }` values, widening a scalar/tuple into a
//! declared `+`-typed (forced-disjoint) Kind, and narrowing a `TaggedUnion`
//! back down to a plain scalar — split out of `mod.rs` as a pure refactor
//! (no behaviour change) to keep that file under the repo's line-count
//! guideline.

use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{
    error::CompileError,
    kind::Kind,
    semantics::tree::{SemExpr, flatten_disjoint_union},
};

use super::{Compiler, wire::tagged_union_leaf_count};

impl<'ctx> Compiler<'ctx> {
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
        let struct_ty = self
            .kind_to_llvm_type(&Kind::TaggedUnion(all_arms.to_vec()))
            .into_struct_type();
        let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
        agg = self
            .builder
            .build_insert_value(agg, tag, 0, "tu_tag")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let mut field_idx = 1u32;
        self.insert_kind_leaves(&mut agg, arm_value, arm_kind, &mut field_idx)?;
        Ok(agg.into_struct_value().into())
    }

    /// Low-level: copy the leaf i64 fields from a TaggedUnion struct into a
    /// (possibly wider) merged struct, using `new_tag` as the tag field.
    ///
    /// Extra i64 leaf fields beyond `old_leaf_count` are left undef — safe because
    /// they are only ever read via the arm that originally wrote them.
    pub(super) fn rewrap_tagged_union_with_tag(
        &self,
        val: BasicValueEnum<'ctx>,
        old_arms: &[Kind],
        new_arms: &[Kind],
        new_tag: inkwell::values::IntValue<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let old_leaf_count = tagged_union_leaf_count(old_arms);
        let new_struct_ty = self
            .kind_to_llvm_type(&Kind::TaggedUnion(new_arms.to_vec()))
            .into_struct_type();
        let old_struct = AggregateValueEnum::StructValue(val.into_struct_value());
        let mut agg: AggregateValueEnum<'ctx> = new_struct_ty.get_undef().into();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        agg = self
            .builder
            .build_insert_value(agg, new_tag, 0, "tu_rw_t")
            .map_err(err)?;
        for i in 0..old_leaf_count {
            let leaf = self
                .builder
                .build_extract_value(old_struct, (i + 1) as u32, "tu_rw_l")
                .map_err(err)?;
            agg = self
                .builder
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
        let tag = self
            .builder
            .build_extract_value(old_struct, 0, "tu_rw_tag")
            .map_err(|e| CompileError::ice(e.to_string()))?
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
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        // Default: the last arm's new index (used when no earlier select fires).
        let mut current = i32t.const_int(*mapping.last().unwrap() as u64, false);
        // Build selects in reverse order so the chain evaluates correctly.
        for (old_idx, &new_idx) in mapping[..mapping.len() - 1].iter().enumerate().rev() {
            let is_this = self
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    old_tag,
                    i32t.const_int(old_idx as u64, false),
                    "tu_tag_eq",
                )
                .map_err(err)?;
            current = self
                .builder
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
        function: inkwell::values::FunctionValue<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let fn_name = function.get_name().to_str().unwrap_or("");
        let expected = self
            .fn_return_kinds
            .get(fn_name)
            .cloned()
            .unwrap_or_else(|| val_kind.clone());
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
            Kind::Int | Kind::Bool => {
                self.compile_scalar_as_singleton_vector(val, &val_kind, &elem_kind)
            }
            other => Err(CompileError::ice(format!(
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
        function: inkwell::values::FunctionValue<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let fn_name = function.get_name().to_str().unwrap_or("");
        let expected = self
            .fn_return_kinds
            .get(fn_name)
            .cloned()
            .unwrap_or_else(|| val_kind.clone());
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
        let set_expr = self
            .fn_param_set_exprs
            .get(callee)
            .and_then(|exprs| exprs.get(arg_idx));
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
        set_expr: Option<&SemExpr>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let arms = match expected {
            Kind::TaggedUnion(a) => a.clone(),
            _ => {
                return match &val_kind {
                    Kind::TaggedUnion(val_arms) => {
                        self.narrow_tagged_union(val, val_arms, expected)
                    }
                    _ => Ok((val, val_kind)),
                };
            }
        };
        if matches!(&val_kind, Kind::TaggedUnion(a) if a == &arms) {
            return Ok((val, val_kind)); // already the right TaggedUnion
        }
        let candidates: Vec<usize> = arms
            .iter()
            .enumerate()
            .filter(|(_, k)| **k == val_kind)
            .map(|(i, _)| i)
            .collect();
        match candidates.as_slice() {
            [] => Err(CompileError::ice(format!(
                "coerce_to_kind: value kind {val_kind:?} does not match any arm of {arms:?}"
            ))),
            [arm_idx] => {
                let wrapped = self.build_tagged_union_value(*arm_idx, val, &val_kind, &arms)?;
                Ok((wrapped, expected.clone()))
            }
            _ => {
                let set_expr = set_expr.ok_or_else(|| {
                    CompileError::ice(format!(
                        "coerce_to_kind: value kind {val_kind:?} matches multiple arms of {arms:?} \
                     but no set expression was recorded to disambiguate them"
                    ))
                })?;
                let wrapped =
                    self.select_disjoint_union_arm(val, &val_kind, &arms, &candidates, set_expr)?;
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
    ///
    /// Valid *only* when every arm already has the exact same Kind as
    /// `expected` — e.g. unwrapping a `+`-typed value like `{0} + NatPos`
    /// (forced-disjoint, but every arm is `Kind::Int`) back into a
    /// non-disjoint `Int` context. Dropping the tag is sound here because no
    /// information about *which value space* the payload belongs to is lost —
    /// every arm was already that value space.
    ///
    /// Rejects (rather than narrowing) a union with a *mixed* Kind arm, e.g.
    /// `Bool | Nat` (`TaggedUnion([Bool, Int])`) narrowed to `Bool`: Bool and
    /// Int are disjoint in Cantor's value model, so an Int-arm payload is not
    /// a valid boolean and must not be silently truncated into one. There is
    /// no language construct yet to inspect which arm a mixed-Kind
    /// `TaggedUnion` value actually holds at runtime, so narrowing one down
    /// to a single arm's Kind can only be done when it's unconditionally true
    /// of every arm.
    fn narrow_tagged_union(
        &self,
        val: BasicValueEnum<'ctx>,
        val_arms: &[Kind],
        expected: &Kind,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let supported =
            matches!(expected, Kind::Int | Kind::Bool) && val_arms.iter().all(|k| k == expected);
        if !supported {
            return Err(CompileError::ice(format!(
                "narrow_tagged_union: cannot narrow a TaggedUnion with arms {val_arms:?} down to \
                 {expected:?} — every arm must already be {expected:?} for this to be sound \
                 (e.g. `{{0}} + NatPos -> Int` is fine; `Bool | Nat -> Bool` is not, since a Nat \
                 arm is not a valid Bool)"
            )));
        }
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let payload = self
            .builder
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
        set_expr: &SemExpr,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let arm_exprs = flatten_disjoint_union(set_expr);
        if arm_exprs.len() != arms.len() {
            return Err(CompileError::ice(format!(
                "select_disjoint_union_arm: not yet implemented for a Kind whose TaggedUnion \
                 arms ({}) don't align with a top-level `+` chain in the recorded set \
                 expression ({} parts) — only plain `A + B + …` domains/ranges are supported today",
                arms.len(),
                arm_exprs.len()
            )));
        }

        let i32t = self.context.i32_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let val_int = val.into_int_value();

        let (&last, rest) = candidates.split_last().ok_or_else(|| {
            CompileError::ice("select_disjoint_union_arm: called with no candidate arms")
        })?;
        let mut tag = i32t.const_int(last as u64, false);
        for &candidate in rest.iter().rev() {
            let in_arm = self.compile_membership(val_int, arm_exprs[candidate])?;
            let candidate_tag = i32t.const_int(candidate as u64, false);
            tag = self
                .builder
                .build_select(in_arm, candidate_tag, tag, "tu_arm_sel")
                .map_err(err)?
                .into_int_value();
        }

        self.build_tagged_union_value_with_tag(tag, val, val_kind, arms)
    }
}
