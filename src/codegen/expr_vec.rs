/// Vector compilation helpers — split from `expr.rs` to keep file size under 1000 lines.
///
/// Contains:
///   • `vec_builder_fns`               — dispatch table for scalar/nested/struct vec ABI
///   • `compile_index`                 — `xs[i]` runtime indexing
///   • `compile_proj`                  — `xs.N` / `xs[N]` literal-index projection
///   • `compile_tuple_as_vector`       — array literal → Arrow vector (entry point)
///   • `compile_tuple_as_struct_vec`   — helper for Tuple element kind
///   • `compile_tuple_as_union_vec`    — helper for TaggedUnion element kind (NEW)
///   • `extract_union_leaves`          — flatten a value's leaves for union push (NEW)
///   • `compile_union_vec_index`       — `xs[i]` for TaggedUnion element kind (NEW)
///   • `compile_scalar_as_singleton_vector`
///   • `compile_struct_vec_index`
use inkwell::values::{AggregateValueEnum, BasicValueEnum};

use crate::{error::CompileError, kind::Kind, semantics::tree::SemExpr};

use super::wire::{leaf_count, tagged_union_leaf_count};

use super::{Compiler, Env};

/// Builder/get function names keyed by the *element* kind of a vector.
///
/// Returns `(new, push, finish, len)` for `Kind::Vector(elem_kind)`.
/// For scalar elements the push arg is the element value (i64).
/// For vector elements the push arg is an i64 pointer to the inner vector —
/// the generic `cantor_list_vec_*` functions are used regardless of depth.
///
/// TaggedUnion and Union element kinds are NOT handled here because they use a
/// different multi-step ABI (builder_new / set_arm / push_leaf / finish).
fn vec_builder_fns(
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
    pub(crate) fn compile_index(
        &self,
        base: &SemExpr,
        index: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (base_val, base_kind) = self.compile_expr(base, env)?;
        let (idx_val, _idx_kind) = self.compile_expr(index, env)?;

        let (get_fn, elem_kind) = match &base_kind {
            Kind::Vector(ek) => {
                let fn_name = match ek.as_ref() {
                    Kind::Int => "cantor_vec_get_i64",
                    Kind::Bool => "cantor_vec_get_bool",
                    Kind::Vector(_) => "cantor_list_vec_get",
                    Kind::Tuple(field_kinds) => {
                        let fk = field_kinds.clone();
                        return self.compile_struct_vec_index(base_val, idx_val, &fk);
                    }
                    Kind::TaggedUnion(arms) => {
                        let arms = arms.clone();
                        return self.compile_union_vec_index(base_val, idx_val, &arms);
                    }
                    other => {
                        return Err(CompileError::ice(format!(
                            "TODO: `xs[i]` not yet implemented for element kind {other:?}"
                        )));
                    }
                };
                (fn_name, ek.as_ref().clone())
            }
            other => {
                return Err(CompileError::ice(format!(
                    "`xs[i]` requires a vector (X*) base, got {other:?}"
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
        Ok((result_val, elem_kind))
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
            match ek.as_ref() {
                Kind::Tuple(field_kinds) => {
                    let idx_val = self
                        .context
                        .i64_type()
                        .const_int(index as u64, false)
                        .into();
                    let fk = field_kinds.clone();
                    return self.compile_struct_vec_index(base_val, idx_val, &fk);
                }
                Kind::TaggedUnion(arms) => {
                    let idx_val = self
                        .context
                        .i64_type()
                        .const_int(index as u64, false)
                        .into();
                    let arms = arms.clone();
                    return self.compile_union_vec_index(base_val, idx_val, &arms);
                }
                _ => {
                    let idx_val = self.context.i64_type().const_int(index as u64, false);
                    let (get_fn, elem_kind) = match ek.as_ref() {
                        Kind::Int => ("cantor_vec_get_i64", Kind::Int),
                        Kind::Bool => ("cantor_vec_get_bool", Kind::Bool),
                        Kind::Vector(inner) => ("cantor_list_vec_get", Kind::Vector(inner.clone())),
                        other => {
                            return Err(CompileError::ice(format!(
                                "xs[N]: unsupported element kind {other:?}"
                            )));
                        }
                    };
                    let fn_val = self.module.get_function(get_fn).ok_or_else(|| {
                        CompileError::ice(format!("runtime function `{get_fn}` not declared"))
                    })?;
                    let base_i64 = base_val.into_int_value();
                    let result = self
                        .builder
                        .build_call(fn_val, &[base_i64.into(), idx_val.into()], "vec_proj")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let result_val = result.try_as_basic_value().left().ok_or_else(|| {
                        CompileError::ice(format!("`{get_fn}` returned void unexpectedly"))
                    })?;
                    return Ok((result_val, elem_kind));
                }
            }
        }

        // TaggedUnion LLVM struct: { i32 tag, i64 leaf_0, … }.  Projection .N
        // extracts field N directly; leaves are raw i64 (Kind::Int).
        if let Kind::TaggedUnion(_) = &base_kind {
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
                (_, Kind::Bool) => self
                    .builder
                    .build_int_z_extend(elem.into_int_value(), i64t, "vec_elem_ext")
                    .map_err(err)?
                    .into(),
                _ => elem,
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
            Kind::Int | Kind::Int64 | Kind::Set(_) | Kind::Vector(_) => Ok(vec![val]),
            Kind::Bool | Kind::Fail => {
                let wide = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "ul_b")
                    .map_err(err)?;
                Ok(vec![wide.into()])
            }
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

        let push_val: BasicValueEnum<'ctx> = if *val_kind == Kind::Bool {
            self.builder
                .build_int_z_extend(
                    val.into_int_value(),
                    self.context.i64_type(),
                    "singleton_ext",
                )
                .map_err(err)?
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
