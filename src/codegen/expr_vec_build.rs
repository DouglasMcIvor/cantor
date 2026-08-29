/// Vector-construction helpers — split from `expr_vec.rs` to keep file size
/// under 1000 lines. `expr_vec.rs` keeps the read side (`xs[i]`/`xs.N`); this
/// file is the write side (turning an LLVM tuple aggregate into an Arrow
/// vector).
///
/// Contains:
///   • `vec_builder_fns`               — dispatch table for scalar/nested/struct vec ABI
///   • `compile_tuple_as_vector`       — array literal → Arrow vector (entry point)
///   • `compile_tuple_as_struct_vec`   — helper for Tuple element kind
///   • `compile_tuple_as_union_vec`    — helper for TaggedUnion element kind
///   • `extract_union_leaves`          — flatten a value's leaves for union push
///   • `compile_scalar_as_singleton_vector`
use inkwell::values::{AggregateValueEnum, BasicValueEnum};

use crate::{error::CompileError, kind::Kind};

use super::wire::leaf_count;

use super::Compiler;

/// Builder/get function names keyed by the *element* kind of a vector.
///
/// Returns `(new, push, finish, len)` for `Kind::Vector(elem_kind)`.
/// For scalar elements the push arg is the element value (i64).
/// For vector elements the push arg is an i64 pointer to the inner vector —
/// the generic `cantor_list_vec_*` functions are used regardless of depth.
///
/// TaggedUnion and Union element kinds are NOT handled here because they use a
/// different multi-step ABI (builder_new / set_arm / push_leaf / finish).
pub(super) fn vec_builder_fns(
    ek: &Kind,
) -> Result<(&'static str, &'static str, &'static str, &'static str), String> {
    match ek {
        Kind::Int => Ok((
            "cantor_vec_builder_new_i64",
            "cantor_vec_builder_push_i64",
            "cantor_vec_builder_finish_i64",
            "cantor_vec_len_i64",
        )),
        Kind::Bool => Ok((
            "cantor_vec_builder_new_bool",
            "cantor_vec_builder_push_bool",
            "cantor_vec_builder_finish_bool",
            "cantor_vec_len_bool",
        )),
        // `Char*`/`Signed32*`/`Unsigned32*` (docs/design-decisions.md §13)
        // reuse the plain `_i64` Arrow `Int64Array` family verbatim — zero new
        // runtime code — via the same sign/zero-extend-into-i64 trick already
        // used for Signed32/Unsigned32 union-vector leaves
        // (`extract_union_leaves` below). The i32<->i64 conversion happens at
        // the two call sites (`compile_tuple_as_vector`'s push,
        // `compile_vector_elem_get`'s get), not here.
        Kind::Char | Kind::Signed32 | Kind::Unsigned32 => Ok((
            "cantor_vec_builder_new_i64",
            "cantor_vec_builder_push_i64",
            "cantor_vec_builder_finish_i64",
            "cantor_vec_len_i64",
        )),
        Kind::Vector(_) => Ok((
            "cantor_list_vec_builder_new",
            "cantor_list_vec_builder_push",
            "cantor_list_vec_builder_finish",
            "cantor_list_vec_len",
        )),
        other => Err(format!(
            "vec_builder_fns: unsupported element kind {other:?}"
        )),
    }
}

impl<'ctx> Compiler<'ctx> {
    /// Build an Arrow vector from an LLVM tuple aggregate.
    ///
    /// Dispatches by `elem_kind`:
    ///   - `Tuple(...)` → struct vector (StructArray, one Int64Array column per field)
    ///   - `TaggedUnion(...)` → union vector (DenseUnionArray, StructArray children)
    ///   - `Int`, `Bool`, `Vector(_)` → scalar/nested vector (Int64Array / BooleanArray)
    pub(crate) fn compile_tuple_as_vector(
        &self,
        tuple_val: BasicValueEnum<'ctx>,
        tuple_elems: &[Kind],
        elem_kind: &Kind,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        if let Kind::Tuple(field_kinds) = elem_kind {
            let fk = field_kinds.clone();
            return self.compile_tuple_as_struct_vec(tuple_val, tuple_elems, &fk);
        }
        if let Kind::TaggedUnion(arms) = elem_kind {
            let arms = arms.clone();
            return self.compile_tuple_as_union_vec(tuple_val, tuple_elems, &arms);
        }

        let (new_fn, push_fn, finish_fn, _) =
            vec_builder_fns(elem_kind).map_err(|e| CompileError::ice(e))?;
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        let new_fn_val = self
            .module
            .get_function(new_fn)
            .ok_or_else(|| CompileError::ice(format!("{new_fn} not declared")))?;
        let push_fn_val = self
            .module
            .get_function(push_fn)
            .ok_or_else(|| CompileError::ice(format!("{push_fn} not declared")))?;
        let finish_fn_val = self
            .module
            .get_function(finish_fn)
            .ok_or_else(|| CompileError::ice(format!("{finish_fn} not declared")))?;

        let builder_ptr = self
            .builder
            .build_call(new_fn_val, &[], "vec_builder")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("vec builder new returned void"))?;

        let sv = AggregateValueEnum::StructValue(tuple_val.into_struct_value());
        let i64t = self.context.i64_type();
        for (i, outer_ek) in tuple_elems.iter().enumerate() {
            let elem = self
                .builder
                .build_extract_value(sv, i as u32, "vec_elem")
                .map_err(err)?;

            let push_val: BasicValueEnum<'ctx> = match (elem_kind, outer_ek) {
                (Kind::Vector(inner_ek), Kind::Tuple(inner_elems)) => {
                    let (inner_ptr, _) =
                        self.compile_tuple_as_vector(elem, inner_elems, inner_ek)?;
                    inner_ptr
                }
                (Kind::Vector(_), Kind::Vector(_)) => elem,
                (_, Kind::Bool | Kind::Char | Kind::Unsigned32) => self
                    .builder
                    .build_int_z_extend(elem.into_int_value(), i64t, "vec_elem_ext")
                    .map_err(err)?
                    .into(),
                (_, Kind::Signed32) => self
                    .builder
                    .build_int_s_extend(elem.into_int_value(), i64t, "vec_elem_sext")
                    .map_err(err)?
                    .into(),
                // `Vector(Int)` storage is always a raw (untagged) `Int64`
                // word (docs/int-soundness-plan.md's Step 4b: containers stay
                // Int64-only, deliberately not made arbitrary-precision) —
                // but the element as compiled here may be a *tagged* `Kind::Int`
                // word (small-int shifted, or a boxed BigInt pointer) whenever
                // the enclosing function is tagging-active. Its current
                // representation is `current_bare_int_kind()`, NOT `outer_ek`
                // (a pre-codegen semantic Kind that never distinguishes
                // raw/tagged) — untag from that before pushing. A genuine
                // BigInt element aborts loudly (container-specific message,
                // not `ensure_raw_int64`'s "compiler bug" wording — this is
                // an expected language limitation) rather than silently
                // storing (and later misreading) a truncated/mistagged word.
                //
                // The one exception to "current representation is
                // `current_bare_int_kind()`": an element that is *itself*
                // `Kind::Int64` (the result of a call into a Step-A-promoted
                // function) is already a raw word, even inside a
                // tagging-active caller. Untagging it as if it were tagged
                // halves an even value and dereferences an odd one as a
                // bogus BigInt box — the same Int64-to-Int re-tagging family
                // as the tuple-leaf/Fail-wire/TaggedUnion-arm sites.
                (Kind::Int, _) => {
                    let repr = if *outer_ek == Kind::Int64 {
                        Kind::Int64
                    } else {
                        self.current_bare_int_kind()
                    };
                    self.ensure_raw_int64_container(elem.into_int_value(), &repr)?
                        .into()
                }
                (other_elem_kind, other_outer_kind) => {
                    return Err(CompileError::ice(format!(
                        "compile_tuple_as_vector: no push rule for vector element kind \
                         {other_elem_kind:?} from literal element kind {other_outer_kind:?}"
                    )));
                }
            };
            self.builder
                .build_call(
                    push_fn_val,
                    &[builder_ptr.into(), push_val.into()],
                    "vec_push",
                )
                .map_err(err)?;
        }

        let vec_ptr = self
            .builder
            .build_call(finish_fn_val, &[builder_ptr.into()], "vec_ptr")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("vec builder finish returned void"))?;

        Ok((vec_ptr, Kind::Vector(Box::new(elem_kind.clone()))))
    }

    /// Build a struct-vector (element kind = `Kind::Tuple(field_kinds)`) from an
    /// LLVM aggregate whose elements are themselves inner structs (one per row).
    fn compile_tuple_as_struct_vec(
        &self,
        tuple_val: BasicValueEnum<'ctx>,
        tuple_elems: &[Kind],
        field_kinds: &[Kind],
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let i64t = self.context.i64_type();

        let new_fn = self
            .module
            .get_function("cantor_struct_vec_builder_new")
            .ok_or_else(|| CompileError::ice("cantor_struct_vec_builder_new not declared"))?;
        let push_fn = self
            .module
            .get_function("cantor_struct_vec_builder_push_field")
            .ok_or_else(|| {
                CompileError::ice("cantor_struct_vec_builder_push_field not declared")
            })?;
        let finish_fn = self
            .module
            .get_function("cantor_struct_vec_builder_finish")
            .ok_or_else(|| CompileError::ice("cantor_struct_vec_builder_finish not declared"))?;

        let n_fields_val = i64t.const_int(field_kinds.len() as u64, false);
        let builder_ptr = self
            .builder
            .build_call(new_fn, &[n_fields_val.into()], "sv_builder")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_struct_vec_builder_new returned void"))?;

        let outer_sv = AggregateValueEnum::StructValue(tuple_val.into_struct_value());
        for i in 0..tuple_elems.len() {
            let outer_elem = self
                .builder
                .build_extract_value(outer_sv, i as u32, "sv_row")
                .map_err(err)?;
            let inner_sv = AggregateValueEnum::StructValue(outer_elem.into_struct_value());
            for (j, fk) in field_kinds.iter().enumerate() {
                let field = self
                    .builder
                    .build_extract_value(inner_sv, j as u32, "sv_field")
                    .map_err(err)?;
                let field_i64 = if *fk == Kind::Bool {
                    self.builder
                        .build_int_z_extend(field.into_int_value(), i64t, "sv_field_ext")
                        .map_err(err)?
                        .into()
                } else {
                    field
                };
                let field_idx_val = i64t.const_int(j as u64, false);
                self.builder
                    .build_call(
                        push_fn,
                        &[builder_ptr.into(), field_idx_val.into(), field_i64.into()],
                        "sv_push",
                    )
                    .map_err(err)?;
            }
        }

        let vec_ptr = self
            .builder
            .build_call(finish_fn, &[builder_ptr.into()], "sv_ptr")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_struct_vec_builder_finish returned void"))?;

        Ok((
            vec_ptr,
            Kind::Vector(Box::new(Kind::Tuple(field_kinds.to_vec()))),
        ))
    }

    /// Build a union-vector (element kind = `Kind::TaggedUnion(arms)`) from an
    /// LLVM aggregate.  Each outer element's Kind must match one arm exactly;
    /// the arm index is resolved at compile time from `elem_kinds[i]`.
    ///
    /// Produces a DenseUnionArray pointer returned as i64.
    fn compile_tuple_as_union_vec(
        &self,
        tuple_val: BasicValueEnum<'ctx>,
        elem_kinds: &[Kind],
        all_arms: &[Kind],
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let i64t = self.context.i64_type();

        let new_fn = self
            .module
            .get_function("cantor_union_vec_builder_new")
            .ok_or_else(|| CompileError::ice("cantor_union_vec_builder_new not declared"))?;
        let set_arm_fn = self
            .module
            .get_function("cantor_union_vec_builder_set_arm")
            .ok_or_else(|| CompileError::ice("cantor_union_vec_builder_set_arm not declared"))?;
        let push_fn = self
            .module
            .get_function("cantor_union_vec_builder_push_leaf")
            .ok_or_else(|| CompileError::ice("cantor_union_vec_builder_push_leaf not declared"))?;
        let finish_fn = self
            .module
            .get_function("cantor_union_vec_builder_finish")
            .ok_or_else(|| CompileError::ice("cantor_union_vec_builder_finish not declared"))?;

        let n_arms_val = i64t.const_int(all_arms.len() as u64, false);
        let builder_ptr = self
            .builder
            .build_call(new_fn, &[n_arms_val.into()], "uv_builder")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_union_vec_builder_new returned void"))?;

        // Register leaf counts for all arms.
        for (ai, arm_kind) in all_arms.iter().enumerate() {
            let ai_val = i64t.const_int(ai as u64, false);
            let nl_val = i64t.const_int(leaf_count(arm_kind) as u64, false);
            self.builder
                .build_call(
                    set_arm_fn,
                    &[builder_ptr.into(), ai_val.into(), nl_val.into()],
                    "uv_set_arm",
                )
                .map_err(err)?;
        }

        // Push each element into the builder.
        let outer_sv = AggregateValueEnum::StructValue(tuple_val.into_struct_value());
        for (i, ek) in elem_kinds.iter().enumerate() {
            let elem = self
                .builder
                .build_extract_value(outer_sv, i as u32, "uv_elem")
                .map_err(err)?;

            let arm_idx = all_arms.iter().position(|k| k == ek).ok_or_else(|| {
                CompileError::ice(format!(
                    "compile_tuple_as_union_vec: element kind {ek:?} not found \
                     in arms {all_arms:?}"
                ))
            })?;

            let leaves = self.extract_union_leaves(elem, ek)?;
            let ai_val = i64t.const_int(arm_idx as u64, false);
            for (li, leaf) in leaves.iter().enumerate() {
                let li_val = i64t.const_int(li as u64, false);
                self.builder
                    .build_call(
                        push_fn,
                        &[
                            builder_ptr.into(),
                            ai_val.into(),
                            li_val.into(),
                            (*leaf).into(),
                        ],
                        "uv_push",
                    )
                    .map_err(err)?;
            }
        }

        let vec_ptr = self
            .builder
            .build_call(finish_fn, &[builder_ptr.into()], "uv_ptr")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_union_vec_builder_finish returned void"))?;

        Ok((
            vec_ptr,
            Kind::Vector(Box::new(Kind::TaggedUnion(all_arms.to_vec()))),
        ))
    }

    /// Flatten a runtime value of the given Kind into a `Vec` of i64-typed LLVM values.
    ///
    /// Used when building a union vector: each element's leaves are pushed one-by-one
    /// via `cantor_union_vec_builder_push_leaf`.
    fn extract_union_leaves(
        &self,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
    ) -> Result<Vec<BasicValueEnum<'ctx>>, CompileError> {
        let i64t = self.context.i64_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        match kind {
            Kind::Int | Kind::Int64 | Kind::Rational | Kind::Set(_) | Kind::Vector(_) => {
                Ok(vec![val])
            }
            Kind::Bool | Kind::Fail | Kind::None => {
                let wide = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "ul_b")
                    .map_err(err)?;
                Ok(vec![wide.into()])
            }
            Kind::Signed32 => {
                let wide = self
                    .builder
                    .build_int_s_extend(val.into_int_value(), i64t, "ul_s32")
                    .map_err(err)?;
                Ok(vec![wide.into()])
            }
            Kind::Unsigned32 | Kind::Char => {
                let wide = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "ul_u32")
                    .map_err(err)?;
                Ok(vec![wide.into()])
            }
            Kind::Float32 => Ok(vec![self.widen_scalar_to_i64(val, kind, "ul_f32")?]),
            Kind::Tuple(elems) => {
                let sv = AggregateValueEnum::StructValue(val.into_struct_value());
                let mut leaves = Vec::new();
                for (i, ek) in elems.iter().enumerate() {
                    let field = self
                        .builder
                        .build_extract_value(sv, i as u32, "ul_f")
                        .map_err(err)?;
                    leaves.extend(self.extract_union_leaves(field, ek)?);
                }
                Ok(leaves)
            }
            Kind::TaggedUnion(_) => Err(CompileError::ice(
                "TODO: nested TaggedUnion as a union-vector element is not yet supported",
            )),
        }
    }

    /// Box a scalar (`Int` or `Bool`) value into a singleton Arrow vector.
    pub(crate) fn compile_scalar_as_singleton_vector(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: &Kind,
        elem_kind: &Kind,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (new_fn, push_fn, finish_fn, _) =
            vec_builder_fns(elem_kind).map_err(|e| CompileError::ice(e))?;
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        let new_fn_val = self
            .module
            .get_function(new_fn)
            .ok_or_else(|| CompileError::ice(format!("{new_fn} not declared")))?;
        let push_fn_val = self
            .module
            .get_function(push_fn)
            .ok_or_else(|| CompileError::ice(format!("{push_fn} not declared")))?;
        let finish_fn_val = self
            .module
            .get_function(finish_fn)
            .ok_or_else(|| CompileError::ice(format!("{finish_fn} not declared")))?;

        let builder_ptr = self
            .builder
            .build_call(new_fn_val, &[], "singleton_builder")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("singleton builder new returned void"))?;

        // Same push-side untagging as `compile_tuple_as_vector` — `Vector(Int)`
        // storage is always raw `Int64`, so a tagged `Kind::Int` value (per
        // `current_bare_int_kind()`, not `val_kind`, which never distinguishes
        // raw/tagged) needs converting down before it's pushed.
        let push_val: BasicValueEnum<'ctx> = if matches!(val_kind, Kind::Bool | Kind::Char) {
            self.builder
                .build_int_z_extend(
                    val.into_int_value(),
                    self.context.i64_type(),
                    "singleton_ext",
                )
                .map_err(err)?
                .into()
        } else if matches!(elem_kind, Kind::Int) {
            self.ensure_raw_int64_container(val.into_int_value(), &self.current_bare_int_kind())?
                .into()
        } else {
            val
        };

        self.builder
            .build_call(
                push_fn_val,
                &[builder_ptr.into(), push_val.into()],
                "singleton_push",
            )
            .map_err(err)?;

        let vec_ptr = self
            .builder
            .build_call(finish_fn_val, &[builder_ptr.into()], "singleton_ptr")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("singleton builder finish returned void"))?;

        Ok((vec_ptr, Kind::Vector(Box::new(elem_kind.clone()))))
    }
}
