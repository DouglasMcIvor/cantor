use inkwell::{
    OptimizationLevel, context::Context, execution_engine::ExecutionEngine, values::FunctionValue,
};

use crate::{ast::Item, error::CompileError, solver::ConstrainedTree};

use super::{Compiler, compile_elaborated, compile_items};

impl<'ctx> Compiler<'ctx> {
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
                (
                    "cantor_set_new_i64",
                    runtime::cantor_set_new_i64 as *const () as usize,
                ),
                (
                    "cantor_set_insert_i64",
                    runtime::cantor_set_insert_i64 as *const () as usize,
                ),
                (
                    "cantor_set_contains_i64",
                    runtime::cantor_set_contains_i64 as *const () as usize,
                ),
                (
                    "cantor_set_size_i64",
                    runtime::cantor_set_size_i64 as *const () as usize,
                ),
                (
                    "cantor_set_get_i64",
                    runtime::cantor_set_get_i64 as *const () as usize,
                ),
                (
                    "cantor_set_new_bool",
                    runtime::cantor_set_new_bool as *const () as usize,
                ),
                (
                    "cantor_set_insert_bool",
                    runtime::cantor_set_insert_bool as *const () as usize,
                ),
                (
                    "cantor_set_contains_bool",
                    runtime::cantor_set_contains_bool as *const () as usize,
                ),
                (
                    "cantor_set_size_bool",
                    runtime::cantor_set_size_bool as *const () as usize,
                ),
                (
                    "cantor_set_get_bool",
                    runtime::cantor_set_get_bool as *const () as usize,
                ),
                // Vector(Int) — Apache Arrow Int64Array
                (
                    "cantor_vec_builder_new_i64",
                    runtime::cantor_vec_builder_new_i64 as *const () as usize,
                ),
                (
                    "cantor_vec_builder_push_i64",
                    runtime::cantor_vec_builder_push_i64 as *const () as usize,
                ),
                (
                    "cantor_vec_builder_finish_i64",
                    runtime::cantor_vec_builder_finish_i64 as *const () as usize,
                ),
                (
                    "cantor_vec_len_i64",
                    runtime::cantor_vec_len_i64 as *const () as usize,
                ),
                (
                    "cantor_vec_get_i64",
                    runtime::cantor_vec_get_i64 as *const () as usize,
                ),
                (
                    "cantor_vec_push_i64",
                    runtime::cantor_vec_push_i64 as *const () as usize,
                ),
                // Vector(Bool) — Apache Arrow BooleanArray
                (
                    "cantor_vec_builder_new_bool",
                    runtime::cantor_vec_builder_new_bool as *const () as usize,
                ),
                (
                    "cantor_vec_builder_push_bool",
                    runtime::cantor_vec_builder_push_bool as *const () as usize,
                ),
                (
                    "cantor_vec_builder_finish_bool",
                    runtime::cantor_vec_builder_finish_bool as *const () as usize,
                ),
                (
                    "cantor_vec_len_bool",
                    runtime::cantor_vec_len_bool as *const () as usize,
                ),
                (
                    "cantor_vec_get_bool",
                    runtime::cantor_vec_get_bool as *const () as usize,
                ),
                (
                    "cantor_vec_push_bool",
                    runtime::cantor_vec_push_bool as *const () as usize,
                ),
                // Concatenation
                (
                    "cantor_vec_concat_i64",
                    runtime::cantor_vec_concat_i64 as *const () as usize,
                ),
                (
                    "cantor_vec_concat_bool",
                    runtime::cantor_vec_concat_bool as *const () as usize,
                ),
                // Nested vectors (X** at any depth) — generic CantorListVec
                (
                    "cantor_list_vec_builder_new",
                    runtime::cantor_list_vec_builder_new as *const () as usize,
                ),
                (
                    "cantor_list_vec_builder_push",
                    runtime::cantor_list_vec_builder_push as *const () as usize,
                ),
                (
                    "cantor_list_vec_builder_finish",
                    runtime::cantor_list_vec_builder_finish as *const () as usize,
                ),
                (
                    "cantor_list_vec_len",
                    runtime::cantor_list_vec_len as *const () as usize,
                ),
                (
                    "cantor_list_vec_get",
                    runtime::cantor_list_vec_get as *const () as usize,
                ),
                (
                    "cantor_list_vec_concat",
                    runtime::cantor_list_vec_concat as *const () as usize,
                ),
                // Struct vectors ((A * B)*)
                (
                    "cantor_struct_vec_builder_new",
                    runtime::cantor_struct_vec_builder_new as *const () as usize,
                ),
                (
                    "cantor_struct_vec_builder_push_field",
                    runtime::cantor_struct_vec_builder_push_field as *const () as usize,
                ),
                (
                    "cantor_struct_vec_builder_finish",
                    runtime::cantor_struct_vec_builder_finish as *const () as usize,
                ),
                (
                    "cantor_struct_vec_len",
                    runtime::cantor_struct_vec_len as *const () as usize,
                ),
                (
                    "cantor_struct_vec_get_field",
                    runtime::cantor_struct_vec_get_field as *const () as usize,
                ),
                (
                    "cantor_struct_vec_concat",
                    runtime::cantor_struct_vec_concat as *const () as usize,
                ),
                // Union vectors ((A | B)* with at least one Tuple arm)
                (
                    "cantor_union_vec_builder_new",
                    runtime::cantor_union_vec_builder_new as *const () as usize,
                ),
                (
                    "cantor_union_vec_builder_set_arm",
                    runtime::cantor_union_vec_builder_set_arm as *const () as usize,
                ),
                (
                    "cantor_union_vec_builder_push_leaf",
                    runtime::cantor_union_vec_builder_push_leaf as *const () as usize,
                ),
                (
                    "cantor_union_vec_builder_finish",
                    runtime::cantor_union_vec_builder_finish as *const () as usize,
                ),
                (
                    "cantor_union_vec_len",
                    runtime::cantor_union_vec_len as *const () as usize,
                ),
                (
                    "cantor_union_vec_get_tag",
                    runtime::cantor_union_vec_get_tag as *const () as usize,
                ),
                (
                    "cantor_union_vec_get_leaf",
                    runtime::cantor_union_vec_get_leaf as *const () as usize,
                ),
                (
                    "cantor_union_vec_concat",
                    runtime::cantor_union_vec_concat as *const () as usize,
                ),
                (
                    "cantor_overflow_abort",
                    runtime::cantor_overflow_abort as *const () as usize,
                ),
                (
                    "cantor_dispatch_unreachable",
                    runtime::cantor_dispatch_unreachable as *const () as usize,
                ),
                (
                    "cantor_bigint_from_i64",
                    runtime::cantor_bigint_from_i64 as *const () as usize,
                ),
                (
                    "cantor_bigint_to_i64",
                    runtime::cantor_bigint_to_i64 as *const () as usize,
                ),
                (
                    "cantor_bigint_add",
                    runtime::cantor_bigint_add as *const () as usize,
                ),
                (
                    "cantor_bigint_sub",
                    runtime::cantor_bigint_sub as *const () as usize,
                ),
                (
                    "cantor_bigint_mul",
                    runtime::cantor_bigint_mul as *const () as usize,
                ),
                (
                    "cantor_bigint_div",
                    runtime::cantor_bigint_div as *const () as usize,
                ),
                (
                    "cantor_bigint_neg",
                    runtime::cantor_bigint_neg as *const () as usize,
                ),
                (
                    "cantor_bigint_cmp",
                    runtime::cantor_bigint_cmp as *const () as usize,
                ),
                (
                    "cantor_bigint_to_string",
                    runtime::cantor_bigint_to_string as *const () as usize,
                ),
            ];
            rt.iter()
                .filter_map(|&(name, addr)| self.module.get_function(name).map(|f| (f, addr)))
                .collect()
        }; // borrow of self.module ends here

        self.module.verify().map_err(|e| e.to_string())?;

        let ee = self
            .module
            .create_jit_execution_engine(OptimizationLevel::None)
            .map_err(|e| e.to_string())?;

        for (fn_val, addr) in mappings {
            ee.add_global_mapping(&fn_val, addr);
        }

        Ok(ee)
    }
}

/// Compile a parsed file to a JIT execution engine.
pub fn compile_file<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
) -> Result<ExecutionEngine<'ctx>, CompileError> {
    compile_items(ctx, items)?
        .into_jit_engine()
        .map_err(|e| CompileError::ice(e))
}

/// Compile an already fully-proved file to a JIT execution engine, without
/// re-running `elaborate()` — the `solver`-verified counterpart to
/// `compile_file`. Only reachable once `solver::check_file` has returned a
/// `ConstrainedTree`, so this is the entry point `cantor run` should use.
///
/// `path`/`src` are baked into any overflow-abort message this file's
/// arithmetic needs (`path:line:col: ...`, matching `main.rs`'s
/// `print_compile_error`) — both already in scope at this function's only
/// call site (`main.rs`'s `run_main`).
pub fn compile_constrained<'ctx>(
    ctx: &'ctx Context,
    tree: &ConstrainedTree,
    path: &str,
    src: &str,
) -> Result<ExecutionEngine<'ctx>, CompileError> {
    compile_elaborated(
        ctx,
        &tree.items,
        &tree.sem_items,
        tree.overflow_checks.clone(),
        Some((path.to_string(), src.to_string())),
        tree.overload_resolution.clone(),
    )?
    .into_jit_engine()
    .map_err(|e| CompileError::ice(e))
}
