use inkwell::{OptimizationLevel, context::Context, execution_engine::ExecutionEngine, values::FunctionValue};

use crate::{ast::Item, error::CompileError};

use super::{Compiler, compile_items};

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
                ("cantor_set_new_i64",       runtime::cantor_set_new_i64       as *const () as usize),
                ("cantor_set_insert_i64",    runtime::cantor_set_insert_i64    as *const () as usize),
                ("cantor_set_contains_i64",  runtime::cantor_set_contains_i64  as *const () as usize),
                ("cantor_set_size_i64",      runtime::cantor_set_size_i64      as *const () as usize),
                ("cantor_set_get_i64",       runtime::cantor_set_get_i64       as *const () as usize),
                ("cantor_set_new_bool",      runtime::cantor_set_new_bool      as *const () as usize),
                ("cantor_set_insert_bool",   runtime::cantor_set_insert_bool   as *const () as usize),
                ("cantor_set_contains_bool", runtime::cantor_set_contains_bool as *const () as usize),
                ("cantor_set_size_bool",     runtime::cantor_set_size_bool     as *const () as usize),
                ("cantor_set_get_bool",      runtime::cantor_set_get_bool      as *const () as usize),
            ];
            rt.iter()
                .filter_map(|&(name, addr)| self.module.get_function(name).map(|f| (f, addr)))
                .collect()
        }; // borrow of self.module ends here

        let ee = self.module
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
        .map_err(CompileError::Internal)
}
