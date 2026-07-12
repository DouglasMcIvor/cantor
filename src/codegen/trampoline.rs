//! `main`'s JIT-boundary trampolines — emitted once per module, after every
//! function body has been compiled, so the Rust caller (`main.rs`'s
//! `run_main`) can call `main()` through a uniform ABI regardless of its
//! Cantor return Kind (fallible scalar vs. tuple). Also home to the MVP IO
//! event loop's trampolines (docs/design-decisions.md §6): `cantor_step` and
//! `cantor_initial_state` (the latter just `emit_into_trampoline` reused).
//!
//! Split out of `mod.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline.

use inkwell::{
    AddressSpace,
    types::BasicTypeEnum,
    values::{AggregateValueEnum, BasicValueEnum, FunctionValue},
};

use crate::{error::CompileError, kind::Kind};

use super::{Compiler, JIT_RUNNER_SENTINEL};

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
    pub(super) fn emit_fallible_main_runner(
        &self,
        main_fn: FunctionValue<'ctx>,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();

        // Global that the runner fills with the error code on failure.
        let fail_code_global = self.module.add_global(i64t, None, "__cantor_fail_code");
        fail_code_global.set_initializer(&i64t.const_int(0, false));

        let runner =
            self.module
                .add_function("__cantor_main_runner", i64t.fn_type(&[], false), None);

        let entry_bb = self.context.append_basic_block(runner, "entry");
        let fail_bb = self.context.append_basic_block(runner, "fail");
        let ok_bb = self.context.append_basic_block(runner, "ok");

        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        self.builder.position_at_end(entry_bb);
        let call = self
            .builder
            .build_call(main_fn, &[], "main_result")
            .map_err(err)?;
        let struct_val = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("main returned void in runner"))?
            .into_struct_value();
        let flag = self
            .builder
            .build_extract_value(struct_val, 0, "runner_flag")
            .map_err(err)?
            .into_int_value();
        self.builder
            .build_conditional_branch(flag, fail_bb, ok_bb)
            .map_err(err)?;

        self.builder.position_at_end(fail_bb);
        let error_code = self
            .builder
            .build_extract_value(struct_val, 1, "runner_err_code")
            .map_err(err)?;
        let fail_code_ptr = fail_code_global.as_pointer_value();
        self.builder
            .build_store(fail_code_ptr, error_code)
            .map_err(err)?;
        let sentinel = i64t.const_int(JIT_RUNNER_SENTINEL as u64, true);
        self.builder.build_return(Some(&sentinel)).map_err(err)?;

        self.builder.position_at_end(ok_bb);
        let payload = self
            .builder
            .build_extract_value(struct_val, 1, "runner_payload")
            .map_err(err)?;
        self.builder.build_return(Some(&payload)).map_err(err)?;

        // Emit a getter so Rust can read the error code via JIT without needing
        // inkwell's (missing) `get_global_value_address` API.
        let getter =
            self.module
                .add_function("__cantor_get_fail_code", i64t.fn_type(&[], false), None);
        let getter_bb = self.context.append_basic_block(getter, "entry");
        self.builder.position_at_end(getter_bb);
        let loaded = self
            .builder
            .build_load(i64t, fail_code_global.as_pointer_value(), "fail_code")
            .map_err(err)?;
        self.builder.build_return(Some(&loaded)).map_err(err)?;

        Ok(())
    }

    /// Emit `void @<exported_name>(ptr %out)` which calls a zero-arg function
    /// (struct or scalar return) and stores every i64 leaf of the result into
    /// the caller-supplied buffer. Booleans are zero-extended to i64 before
    /// storing. Originally `main`-specific (hence `cantor_main_into`, still
    /// the name used for `main`'s own trampoline); generalized so the MVP
    /// event loop (docs/design-decisions.md §6) can reuse it verbatim to emit
    /// `cantor_initial_state` from the 0-arity `main : -> S` seed overload —
    /// `trampoline_store_leaves` already handles every `Kind` uniformly, the
    /// restriction to `Kind::Tuple` lived only in the caller, not here.
    pub(super) fn emit_into_trampoline(
        &self,
        target_fn: FunctionValue<'ctx>,
        ret_kind: &Kind,
        exported_name: &str,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();
        let ptr_t = self.context.ptr_type(AddressSpace::default());
        let fn_type = self.context.void_type().fn_type(&[ptr_t.into()], false);
        let trampoline = self.module.add_function(exported_name, fn_type, None);

        let bb = self.context.append_basic_block(trampoline, "entry");
        self.builder.position_at_end(bb);

        let out_ptr = trampoline.get_nth_param(0).unwrap().into_pointer_value();

        let call = self
            .builder
            .build_call(target_fn, &[], "into_result")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let result = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("target returned void in trampoline"))?;

        let mut leaf_idx = 0usize;
        Self::trampoline_store_leaves(
            &self.builder,
            result,
            ret_kind,
            out_ptr,
            i64t,
            &mut leaf_idx,
        )?;

        self.builder
            .build_return(None)
            .map_err(|e| CompileError::ice(e.to_string()))?;
        Ok(())
    }

    /// Emit `void @cantor_step(ptr %in, ptr %out)` for the MVP event loop
    /// (docs/design-decisions.md §6): loads `(Event, State)` leaves from
    /// `%in`, calls the 2-arity event-loop `main`, and stores the resulting
    /// `(Output, State)` leaves into `%out` — the mirror image of
    /// [`Self::emit_into_trampoline`], with an input buffer to load call
    /// arguments from instead of an empty argument list.
    pub(super) fn emit_event_loop_step(
        &self,
        step_fn: FunctionValue<'ctx>,
        event_kind: &Kind,
        state_kind: &Kind,
        output_kind: &Kind,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();
        let ptr_t = self.context.ptr_type(AddressSpace::default());
        let fn_type = self
            .context
            .void_type()
            .fn_type(&[ptr_t.into(), ptr_t.into()], false);
        let trampoline = self.module.add_function("cantor_step", fn_type, None);

        let bb = self.context.append_basic_block(trampoline, "entry");
        self.builder.position_at_end(bb);

        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        let in_ptr = trampoline.get_nth_param(0).unwrap().into_pointer_value();
        let out_ptr = trampoline.get_nth_param(1).unwrap().into_pointer_value();

        let mut leaf_idx = 0usize;
        let event_val = self.trampoline_load_leaves(event_kind, in_ptr, i64t, &mut leaf_idx)?;
        let state_val = self.trampoline_load_leaves(state_kind, in_ptr, i64t, &mut leaf_idx)?;

        let call = self
            .builder
            .build_call(
                step_fn,
                &[event_val.into(), state_val.into()],
                "step_result",
            )
            .map_err(err)?;
        let result = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("event-loop main returned void in trampoline"))?;

        let out_kind = Kind::Tuple(vec![output_kind.clone(), state_kind.clone()]);
        let mut out_leaf_idx = 0usize;
        Self::trampoline_store_leaves(
            &self.builder,
            result,
            &out_kind,
            out_ptr,
            i64t,
            &mut out_leaf_idx,
        )?;

        self.builder.build_return(None).map_err(err)?;
        Ok(())
    }

    /// Reconstruct a value of `kind`, suitable for use as a call argument, by
    /// reading flat i64 leaves from `in_ptr` starting at `*leaf_idx`. Mirror
    /// image of [`Self::trampoline_store_leaves`]: that widens native-width
    /// values *up* to i64 for storage, this truncates *back down* to the
    /// natural width `declare_function`'s calling convention expects inside
    /// an aggregate (a top-level scalar/Vector param crosses the ABI boundary
    /// as a bare i64 regardless of Kind — see `declare_function` — so only
    /// the `Tuple` case needs any truncation at all; scalars pass the loaded
    /// word straight through unchanged).
    fn trampoline_load_leaves(
        &self,
        kind: &Kind,
        in_ptr: inkwell::values::PointerValue<'ctx>,
        i64t: inkwell::types::IntType<'ctx>,
        leaf_idx: &mut usize,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let load_word =
            |leaf_idx: &mut usize| -> Result<inkwell::values::IntValue<'ctx>, CompileError> {
                let ptr = if *leaf_idx == 0 {
                    in_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    // Safety: GEP into a caller-allocated i64 array; index is
                    // in-bounds because the driver allocates exactly
                    // leaf_count(kind) elements.
                    unsafe {
                        self.builder
                            .build_gep(i64t, in_ptr, &[idx], "lgp")
                            .map_err(err)?
                    }
                };
                let word = self
                    .builder
                    .build_load(i64t, ptr, "lw")
                    .map_err(err)?
                    .into_int_value();
                *leaf_idx += 1;
                Ok(word)
            };
        match kind {
            Kind::Bool | Kind::Fail => {
                let word = load_word(leaf_idx)?;
                let narrow = self
                    .builder
                    .build_int_truncate(word, self.context.bool_type(), "ld_b")
                    .map_err(err)?;
                Ok(narrow.into())
            }
            Kind::Int | Kind::Int64 | Kind::Set(_) | Kind::Vector(_) => {
                Ok(load_word(leaf_idx)?.into())
            }
            Kind::Signed32 | Kind::Unsigned32 | Kind::Char => {
                let word = load_word(leaf_idx)?;
                let narrow = self
                    .builder
                    .build_int_truncate(word, self.context.i32_type(), "ld_w32")
                    .map_err(err)?;
                Ok(narrow.into())
            }
            Kind::Tuple(elems) => {
                let types: Vec<BasicTypeEnum<'ctx>> =
                    elems.iter().map(|k| self.kind_to_llvm_type(k)).collect();
                let struct_ty = self.context.struct_type(&types, false);
                let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
                for (i, ek) in elems.iter().enumerate() {
                    let v = self.trampoline_load_leaves(ek, in_ptr, i64t, leaf_idx)?;
                    agg = self
                        .builder
                        .build_insert_value(agg, v, i as u32, "ld_te")
                        .map_err(err)?;
                }
                Ok(agg.into_struct_value().into())
            }
            // TODO: tagged-union IR — same gap as trampoline_store_leaves.
            Kind::TaggedUnion(_) => Err(CompileError::ice(
                "trampoline_load_leaves: TaggedUnion input not yet supported",
            )),
        }
    }

    fn trampoline_store_leaves(
        builder: &inkwell::builder::Builder<'ctx>,
        val: BasicValueEnum<'ctx>,
        kind: &Kind,
        out_ptr: inkwell::values::PointerValue<'ctx>,
        i64t: inkwell::types::IntType<'ctx>,
        leaf_idx: &mut usize,
    ) -> Result<(), CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        match kind {
            Kind::Bool | Kind::Fail => {
                let wide = builder
                    .build_int_z_extend(val.into_int_value(), i64t, "bl")
                    .map_err(err)?;
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    // Safety: GEP into a caller-allocated i64 array; index is in-bounds
                    // because run_main allocates n_leaves elements.
                    unsafe {
                        builder
                            .build_gep(i64t, out_ptr, &[idx], "gp")
                            .map_err(err)?
                    }
                };
                builder.build_store(ptr, wide).map_err(err)?;
                *leaf_idx += 1;
            }
            Kind::Int | Kind::Int64 | Kind::Set(_) => {
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    // Safety: same as above.
                    unsafe {
                        builder
                            .build_gep(i64t, out_ptr, &[idx], "gp")
                            .map_err(err)?
                    }
                };
                builder
                    .build_store(ptr, val.into_int_value())
                    .map_err(err)?;
                *leaf_idx += 1;
            }
            Kind::Signed32 | Kind::Unsigned32 | Kind::Char => {
                let wide = if *kind == Kind::Signed32 {
                    builder.build_int_s_extend(val.into_int_value(), i64t, "w32")
                } else {
                    builder.build_int_z_extend(val.into_int_value(), i64t, "w32")
                }
                .map_err(err)?;
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    // Safety: same as above.
                    unsafe {
                        builder
                            .build_gep(i64t, out_ptr, &[idx], "gp")
                            .map_err(err)?
                    }
                };
                builder.build_store(ptr, wide).map_err(err)?;
                *leaf_idx += 1;
            }
            Kind::Tuple(elem_kinds) => {
                let sv = AggregateValueEnum::StructValue(val.into_struct_value());
                for (i, ek) in elem_kinds.iter().enumerate() {
                    let elem = builder
                        .build_extract_value(sv, i as u32, "te")
                        .map_err(err)?;
                    Self::trampoline_store_leaves(builder, elem, ek, out_ptr, i64t, leaf_idx)?;
                }
            }
            // TODO: tagged-union IR — emit the raw struct fields for now;
            // a proper trampoline would inspect the tag and decode each arm.
            Kind::TaggedUnion(_) => {
                return Err(CompileError::ice(
                    "trampoline_store_leaves: TaggedUnion output not yet supported",
                ));
            }
            // Vector is an i64 pointer — store it like any other i64 leaf.
            Kind::Vector(_) => {
                let ptr = if *leaf_idx == 0 {
                    out_ptr
                } else {
                    let idx = i64t.const_int(*leaf_idx as u64, false);
                    unsafe {
                        builder
                            .build_gep(i64t, out_ptr, &[idx], "gp")
                            .map_err(err)?
                    }
                };
                builder
                    .build_store(ptr, val.into_int_value())
                    .map_err(err)?;
                *leaf_idx += 1;
            }
        }
        Ok(())
    }
}
