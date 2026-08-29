/// Vector indexing helpers — split from `expr.rs` to keep file size under
/// 1000 lines. The write side (building an Arrow vector from an LLVM tuple
/// literal) lives in `expr_vec_build.rs`.
///
/// Contains:
///   • `compile_index`                 — `xs[i]` runtime indexing
///   • `compile_vector_elem_get`       — shared `xs[i]` get for `Vector(ek)`
///   • `compile_tagged_union_seq_index` — `xs[i]` for a sequence-unification union
///   • `compile_proj`                  — `xs.N` / `xs[N]` literal-index projection
///   • `compile_union_vec_index`       — `xs[i]` for TaggedUnion element kind
///   • `compile_struct_vec_index`      — `xs[i]` for Tuple element kind
///   • `vector_len_fn_name`             — dispatch table for the `len(xs)` runtime call
use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{error::CompileError, kind::Kind, semantics::tree::SemExpr};

use super::wire::tagged_union_leaf_count;

use super::{Compiler, Env};

/// Runtime function name for `len(xs)` where `xs : ek*`, keyed by element kind.
/// Shared by the `len()` builtin (`expr.rs`) and `for x in xs` vector iteration
/// (`loops.rs`), which both need the vector's element count.
pub(crate) fn vector_len_fn_name(ek: &Kind) -> Result<&'static str, CompileError> {
    Ok(match ek {
        Kind::Int => "cantor_vec_len_i64",
        Kind::Bool => "cantor_vec_len_bool",
        Kind::Char | Kind::Signed32 | Kind::Unsigned32 => "cantor_vec_len_i64",
        Kind::Vector(_) => "cantor_list_vec_len",
        Kind::Tuple(_) => "cantor_struct_vec_len",
        Kind::TaggedUnion(_) => "cantor_union_vec_len",
        other => {
            return Err(CompileError::ice(format!(
                "len() on Vector({other:?}) not yet supported"
            )));
        }
    })
}

impl<'ctx> Compiler<'ctx> {
    pub(crate) fn compile_index(
        &self,
        base: &SemExpr,
        index: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (base_val, base_kind) = self.compile_expr(base, env)?;
        let (idx_val, idx_kind) = self.compile_expr(index, env)?;
        // `idx_val` is a *runtime* index (a literal constant index goes
        // through `compile_proj`'s `.N`/`[N]` path instead, never here) —
        // under whole-program BigInt tagging (always active for a real
        // `cantor run`/`cantor build`, see `state_leaf_shape`'s doc comment),
        // a `Kind::Int`/`Nat` variable's raw bits are a *tagged* word (small
        // int shifted left one, or a boxed-BigInt pointer), not the plain
        // integer value — untag it before using it as a raw Arrow array
        // position, the same boundary `compile_tuple_as_vector`'s push side
        // already crosses via `ensure_raw_int64_container` for *elements*.
        // Skipping this let a tagged index silently read (or, once the
        // tagged value ran past the real length, crash on) the wrong
        // element — e.g. logical index 1 read raw position 2.
        let idx_val = self
            .ensure_raw_int64_container(idx_val.into_int_value(), &idx_kind)?
            .into();

        match &base_kind {
            Kind::Vector(ek) => self.compile_vector_elem_get(base_val, ek, idx_val),
            Kind::TaggedUnion(arms) => self.compile_tagged_union_seq_index(base_val, arms, idx_val),
            other => Err(CompileError::ice(format!(
                "`xs[i]` requires a vector (X*) base, got {other:?}"
            ))),
        }
    }

    /// Emit the get call for `xs[i]` where `xs : ek*` — shared by `compile_index`
    /// (expression-position indexing) and `for x in xs` runtime-vector iteration.
    pub(crate) fn compile_vector_elem_get(
        &self,
        base_val: BasicValueEnum<'ctx>,
        ek: &Kind,
        idx_val: BasicValueEnum<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let get_fn = match ek {
            // `Vector(Int)` storage is always a raw (untagged) `Int64` word
            // (see `compile_tuple_as_vector`'s push-side comment) — re-tag it
            // to match the current function's tagging-active `Kind::Int`
            // representation before returning, since the shared call/return
            // path below assumes the raw result IS the element's final
            // representation. A no-op when `!tagging_active()`.
            Kind::Int => {
                let fn_val = self
                    .module
                    .get_function("cantor_vec_get_i64")
                    .ok_or_else(|| {
                        CompileError::ice("runtime function `cantor_vec_get_i64` not declared")
                    })?;
                let base_i64 = base_val.into_int_value();
                let idx_i64 = idx_val.into_int_value();
                let result = self
                    .builder
                    .build_call(fn_val, &[base_i64.into(), idx_i64.into()], "vec_get")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let result_i64 = result.try_as_basic_value().left().ok_or_else(|| {
                    CompileError::ice("`cantor_vec_get_i64` returned void unexpectedly")
                })?;
                let tagged = self.ensure_tagged(result_i64.into_int_value(), &Kind::Int64)?;
                return Ok((tagged.into(), Kind::Int));
            }
            // `cantor_vec_get_bool` returns a raw `i64` (0 or 1) at the ABI
            // boundary (`cantor-runtime/src/lib.rs`), not `Kind::Bool`'s own
            // `i1` LLVM representation (`kind_to_llvm_type`) — truncate and
            // return early, same reason Char/Signed32/Unsigned32 do below,
            // since the shared call/return path past this match assumes the
            // raw call result already IS the element's final LLVM type.
            Kind::Bool => {
                let fn_val = self
                    .module
                    .get_function("cantor_vec_get_bool")
                    .ok_or_else(|| {
                        CompileError::ice("runtime function `cantor_vec_get_bool` not declared")
                    })?;
                let base_i64 = base_val.into_int_value();
                let idx_i64 = idx_val.into_int_value();
                let result = self
                    .builder
                    .build_call(fn_val, &[base_i64.into(), idx_i64.into()], "vec_get")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let result_i64 = result.try_as_basic_value().left().ok_or_else(|| {
                    CompileError::ice("`cantor_vec_get_bool` returned void unexpectedly")
                })?;
                let truncated = self
                    .builder
                    .build_int_truncate(
                        result_i64.into_int_value(),
                        self.context.bool_type(),
                        "vec_get_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                return Ok((truncated.into(), Kind::Bool));
            }
            // `Char*`/`Signed32*`/`Unsigned32*` reuse the `_i64` Arrow storage
            // (`vec_builder_fns`), but the element itself is an i32 register —
            // truncate the i64 read back down and return early, since the
            // shared call/return path below assumes the raw result IS the
            // element's LLVM type. Truncation is bit-identical for the
            // signed/unsigned cases, so one code path covers both.
            Kind::Char | Kind::Signed32 | Kind::Unsigned32 => {
                let fn_val = self
                    .module
                    .get_function("cantor_vec_get_i64")
                    .ok_or_else(|| {
                        CompileError::ice("runtime function `cantor_vec_get_i64` not declared")
                    })?;
                let base_i64 = base_val.into_int_value();
                let idx_i64 = idx_val.into_int_value();
                let result = self
                    .builder
                    .build_call(fn_val, &[base_i64.into(), idx_i64.into()], "vec_get")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let result_i64 = result.try_as_basic_value().left().ok_or_else(|| {
                    CompileError::ice("`cantor_vec_get_i64` returned void unexpectedly")
                })?;
                let truncated = self
                    .builder
                    .build_int_truncate(
                        result_i64.into_int_value(),
                        self.context.i32_type(),
                        "vec_get_i32",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                return Ok((truncated.into(), ek.clone()));
            }
            Kind::Vector(_) => "cantor_list_vec_get",
            Kind::Tuple(field_kinds) => {
                return self.compile_struct_vec_index(base_val, idx_val, field_kinds);
            }
            Kind::TaggedUnion(arms) => {
                return self.compile_union_vec_index(base_val, idx_val, arms);
            }
            other => {
                return Err(CompileError::ice(format!(
                    "TODO: `xs[i]` not yet implemented for element kind {other:?}"
                )));
            }
        };

        let fn_val = self.module.get_function(get_fn).ok_or_else(|| {
            CompileError::ice(format!("runtime function `{get_fn}` not declared"))
        })?;
        let base_i64 = base_val.into_int_value();
        let idx_i64 = idx_val.into_int_value();
        let result = self
            .builder
            .build_call(fn_val, &[base_i64.into(), idx_i64.into()], "vec_get")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let result_val = result
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice(format!("`{get_fn}` returned void unexpectedly")))?;
        // Reached only for `Vector(_)` (an opaque pointer, never tagged) —
        // needs no boundary conversion, unlike every scalar case above.
        Ok((result_val, ek.clone()))
    }

    /// Emit `xs[i]` where `xs : TaggedUnion(arms)` is a "sequence-unification"
    /// union — every arm is either `Vector(ek)` or a bare scalar `ek`, for one
    /// shared `ek` — produced when `^`/`|` bridges a `X*` arm with a scalar
    /// sharing its element Kind (e.g. `Nat* ^ Int`; see the domain comment in
    /// `tests/cantor_files/cross_sort_sym_diff_proof.cantor`). The scalar arm
    /// stands in for an implicit singleton sequence `[x]`.
    ///
    /// Every arm here is single-leaf (`Vector` and scalar Kinds are both one
    /// leaf — see `wire::leaf_count`), so the struct is always `{i32 tag, i64
    /// leaf0}` regardless of which arm is live. `leaf0` decoded per-arm (a
    /// real vector-get for the `Vector` arm, the raw leaf for the scalar arm)
    /// feeds a tag-selected `select` chain.
    ///
    /// Indexing the scalar arm at any index other than 0 only happens for
    /// values a domain proof has already ruled out (e.g. `- Int` above
    /// excludes the scalar arm from ever reaching `xs[1]`) — same trust model
    /// as proved-safe division skipping a runtime zero check, so no bounds
    /// check is emitted here.
    pub(crate) fn compile_tagged_union_seq_index(
        &self,
        base_val: BasicValueEnum<'ctx>,
        arms: &[Kind],
        idx_val: BasicValueEnum<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let elem_kind = arms.iter().find_map(|k| match k {
            Kind::Vector(ek) => Some(ek.as_ref().clone()),
            _ => None,
        });
        let elem_kind = elem_kind.ok_or_else(|| {
            CompileError::ice(
                "TODO: indexing (`.N` / `[i]`) into a `TaggedUnion` is only supported \
                 for a Vector/scalar sequence-unification bridge (e.g. `Nat* ^ Int`); \
                 this union has no `Vector(_)` arm",
            )
        })?;
        if !matches!(elem_kind, Kind::Int | Kind::Bool) {
            return Err(CompileError::ice(format!(
                "TODO: indexing (`.N` / `[i]`) into a `TaggedUnion` sequence-unification \
                 bridge only supports scalar element kind Int/Bool, got {elem_kind:?}"
            )));
        }
        for k in arms {
            let ok = matches!(k, Kind::Vector(ek) if **ek == elem_kind) || *k == elem_kind;
            if !ok {
                return Err(CompileError::ice(format!(
                    "TODO: indexing (`.N` / `[i]`) into a `TaggedUnion` only supports \
                     sequence-unification shapes (every arm `Vector({elem_kind:?})` or \
                     `{elem_kind:?}`); found arm {k:?}"
                )));
            }
        }

        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let base_struct = AggregateValueEnum::StructValue(base_val.into_struct_value());
        let tag = self
            .builder
            .build_extract_value(base_struct, 0, "seq_idx_tag")
            .map_err(err)?
            .into_int_value();
        let leaf0 = self
            .builder
            .build_extract_value(base_struct, 1, "seq_idx_leaf0")
            .map_err(err)?;

        let per_arm_values = arms
            .iter()
            .map(|k| -> Result<BasicValueEnum<'ctx>, CompileError> {
                match k {
                    Kind::Vector(_) => {
                        Ok(self.compile_vector_elem_get(leaf0, &elem_kind, idx_val)?.0)
                    }
                    _ if elem_kind == Kind::Bool => Ok(self
                        .builder
                        .build_int_truncate(
                            leaf0.into_int_value(),
                            self.context.bool_type(),
                            "seq_idx_scalar_bool",
                        )
                        .map_err(err)?
                        .into()),
                    _ => Ok(leaf0),
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        let i32t = self.context.i32_type();
        let mut result = *per_arm_values
            .last()
            .expect("TaggedUnion always has at least one arm");
        for (idx, val) in per_arm_values[..per_arm_values.len() - 1]
            .iter()
            .enumerate()
            .rev()
        {
            let is_this = self
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    tag,
                    i32t.const_int(idx as u64, false),
                    "seq_idx_tag_eq",
                )
                .map_err(err)?;
            result = self
                .builder
                .build_select(is_this, *val, result, "seq_idx_sel")
                .map_err(err)?;
        }

        Ok((result, elem_kind))
    }

    /// Compile `base.N` (or `base[N]` with a literal N) — extract element N.
    ///
    /// For tuple bases this extracts the Nth LLVM struct field.
    /// For vector bases (`(A * B)*`, `X*`) this calls the appropriate Arrow get function.
    pub(crate) fn compile_proj(
        &self,
        base: &SemExpr,
        index: usize,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (base_val, base_kind) = self.compile_expr(base, env)?;

        if let Kind::Vector(ek) = &base_kind {
            let idx_val = self
                .context
                .i64_type()
                .const_int(index as u64, false)
                .into();
            return self.compile_vector_elem_get(base_val, ek, idx_val);
        }

        // A sequence-unification union (`Nat* ^ Int`-shaped; see
        // `compile_tagged_union_seq_index`) reinterprets `.N` as sequence
        // indexing. Any other `TaggedUnion` falls back to the raw LLVM leaf
        // N — `{ i32 tag, i64 leaf_0, … }`, so `.1` is leaf 0, `.2` is leaf
        // 1, etc.; leaves are always plain i64 (`Kind::Int`).
        if let Kind::TaggedUnion(arms) = &base_kind {
            if crate::kind::sequence_unification_elem_kind(arms).is_some() {
                let idx_val = self
                    .context
                    .i64_type()
                    .const_int(index as u64, false)
                    .into();
                return self.compile_tagged_union_seq_index(base_val, arms, idx_val);
            }
            let field_val = self
                .builder
                .build_extract_value(
                    AggregateValueEnum::StructValue(base_val.into_struct_value()),
                    index as u32,
                    "tu_proj",
                )
                .map_err(|e| CompileError::ice(e.to_string()))?;
            return Ok((field_val, Kind::Int));
        }

        let elem_kinds = match base_kind {
            Kind::Tuple(ek) => ek,
            _ => {
                return Err(CompileError::ice(
                    "projection `.N` applied to non-tuple value",
                ));
            }
        };
        if index >= elem_kinds.len() {
            return Err(CompileError::ice(format!(
                "tuple index {index} out of bounds (tuple has {} elements)",
                elem_kinds.len()
            )));
        }
        let elem_val = self
            .builder
            .build_extract_value(
                AggregateValueEnum::StructValue(base_val.into_struct_value()),
                index as u32,
                "proj",
            )
            .map_err(|e| CompileError::ice(e.to_string()))?;
        Ok((elem_val, elem_kinds[index].clone()))
    }

    /// Emit the multi-call get for `xs[i]` where `xs : (A | B | …)*`.
    ///
    /// Calls `cantor_union_vec_get_tag` and then `cantor_union_vec_get_leaf` once
    /// per leaf slot of the widest arm, assembling the result into the standard
    /// `{ i32 tag, i64 leaf_0, … }` TaggedUnion LLVM struct.
    fn compile_union_vec_index(
        &self,
        base_val: BasicValueEnum<'ctx>,
        idx_val: BasicValueEnum<'ctx>,
        arms: &[Kind],
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let i64t = self.context.i64_type();

        let get_tag_fn = self
            .module
            .get_function("cantor_union_vec_get_tag")
            .ok_or_else(|| CompileError::ice("cantor_union_vec_get_tag not declared"))?;
        let get_leaf_fn = self
            .module
            .get_function("cantor_union_vec_get_leaf")
            .ok_or_else(|| CompileError::ice("cantor_union_vec_get_leaf not declared"))?;

        let base_i64 = base_val.into_int_value();
        let idx_i64 = idx_val.into_int_value();

        // Retrieve the arm index (tag) and truncate to i32 for the struct tag field.
        let tag_i64 = self
            .builder
            .build_call(get_tag_fn, &[base_i64.into(), idx_i64.into()], "uv_tag")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_union_vec_get_tag returned void"))?
            .into_int_value();
        let tag_i32 = self
            .builder
            .build_int_truncate(tag_i64, self.context.i32_type(), "uv_tag32")
            .map_err(err)?;

        // Build the { i32 tag, i64 l0, … } result struct.
        let n_leaves = tagged_union_leaf_count(arms);
        let struct_ty = self
            .kind_to_llvm_type(&Kind::TaggedUnion(arms.to_vec()))
            .into_struct_type();
        let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
        agg = self
            .builder
            .build_insert_value(agg, tag_i32, 0, "uv_r_tag")
            .map_err(err)?;

        for li in 0..n_leaves {
            let li_val = i64t.const_int(li as u64, false);
            let leaf = self
                .builder
                .build_call(
                    get_leaf_fn,
                    &[base_i64.into(), idx_i64.into(), li_val.into()],
                    "uv_leaf",
                )
                .map_err(err)?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice("cantor_union_vec_get_leaf returned void"))?;
            agg = self
                .builder
                .build_insert_value(agg, leaf, (li + 1) as u32, "uv_r_l")
                .map_err(err)?;
        }

        Ok((
            agg.into_struct_value().into(),
            Kind::TaggedUnion(arms.to_vec()),
        ))
    }

    /// Emit the multi-call get for `xs[i]` where `xs : (A * B)*`.
    /// Calls `cantor_struct_vec_get_field` once per field and assembles an LLVM struct.
    pub(crate) fn compile_struct_vec_index(
        &self,
        base_val: BasicValueEnum<'ctx>,
        idx_val: BasicValueEnum<'ctx>,
        field_kinds: &[Kind],
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let i64t = self.context.i64_type();

        let get_fn = self
            .module
            .get_function("cantor_struct_vec_get_field")
            .ok_or_else(|| CompileError::ice("cantor_struct_vec_get_field not declared"))?;

        let base_i64 = base_val.into_int_value();
        let idx_i64 = idx_val.into_int_value();

        let llvm_types: Vec<_> = field_kinds
            .iter()
            .map(|k| self.kind_to_llvm_type(k))
            .collect();
        let struct_type = self.context.struct_type(&llvm_types, false);
        let mut agg: AggregateValueEnum<'ctx> = struct_type.get_undef().into();

        for (j, fk) in field_kinds.iter().enumerate() {
            let field_idx = i64t.const_int(j as u64, false);
            let raw = self
                .builder
                .build_call(
                    get_fn,
                    &[base_i64.into(), idx_i64.into(), field_idx.into()],
                    "sv_get_f",
                )
                .map_err(err)?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice("cantor_struct_vec_get_field returned void"))?;
            let field_val = if *fk == Kind::Bool {
                self.builder
                    .build_int_truncate(
                        raw.into_int_value(),
                        self.context.bool_type(),
                        "sv_f_trunc",
                    )
                    .map_err(err)?
                    .into()
            } else {
                raw
            };
            agg = self
                .builder
                .build_insert_value(agg, field_val, j as u32, "sv_row_f")
                .map_err(err)?;
        }

        Ok((
            agg.into_struct_value().into(),
            Kind::Tuple(field_kinds.to_vec()),
        ))
    }
}
