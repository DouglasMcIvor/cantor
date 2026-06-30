//! `main`'s JIT-boundary trampolines — emitted once per module, after every
//! function body has been compiled, so the Rust caller (`main.rs`'s
//! `run_main`) can call `main()` through a uniform ABI regardless of its
//! Cantor return Kind (fallible scalar vs. tuple).
//!
//! Split out of `mod.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline.

use inkwell::{
    AddressSpace,
    context::Context,
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
    pub(super) fn emit_tuple_main_trampoline(
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
            &self.builder, self.context, result, ret_kind, out_ptr, i64t, &mut leaf_idx,
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
