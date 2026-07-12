//! Emit a compiled module as a native object file — the non-JIT
//! counterpart to `jit.rs`'s `into_jit_engine`, used by `cantor build`'s
//! AOT backend (`aot.rs`).

use std::path::Path;

use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};

use crate::{error::CompileError, solver::ConstrainedTree};

use super::compile::compile_elaborated;

/// Verify `module` and write it to `path` as a native object file for the
/// host target, using the host's exact CPU/feature set — mirrors a plain
/// `-C target-cpu=native` build. Fine for a prototype's local `cantor
/// build`; cross-compilation would need a caller-supplied triple/cpu/
/// features instead of the `get_host_*` calls below (not needed yet — no
/// cross-compilation story exists for this project).
pub fn write_object_file(module: &Module, path: &Path) -> Result<(), CompileError> {
    module
        .verify()
        .map_err(|e| CompileError::ice(e.to_string()))?;

    Target::initialize_native(&InitializationConfig::default()).map_err(CompileError::ice)?;

    let triple = TargetMachine::get_default_triple();
    let cpu = TargetMachine::get_host_cpu_name().to_string();
    let features = TargetMachine::get_host_cpu_features().to_string();
    let target = Target::from_triple(&triple).map_err(|e| CompileError::ice(e.to_string()))?;
    let target_machine = target
        .create_target_machine(
            &triple,
            &cpu,
            &features,
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or_else(|| CompileError::ice("failed to create target machine for host triple"))?;

    target_machine
        .write_to_file(module, FileType::Object, path)
        .map_err(|e| CompileError::ice(e.to_string()))
}

/// Compile an already fully-proved file straight to a native object file —
/// the AOT counterpart of `jit.rs`'s `compile_constrained`. Only reachable
/// once `solver::check_file` has returned a `ConstrainedTree`; `cantor
/// build`'s entry point (`aot.rs`) is the only caller.
pub fn compile_constrained_to_object(
    ctx: &Context,
    tree: &ConstrainedTree,
    path: &str,
    src: &str,
    out: &Path,
) -> Result<(), CompileError> {
    let compiler = compile_elaborated(
        ctx,
        &tree.items,
        &tree.sem_items,
        tree.overflow_checks.clone(),
        Some((path.to_string(), src.to_string())),
        tree.overload_resolution.clone(),
    )?;
    write_object_file(compiler.module(), out)
}
