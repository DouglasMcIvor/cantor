//! Emit a compiled module as a native object file — the non-JIT
//! counterpart to `jit.rs`'s `into_jit_engine`, used by `cantor build`'s
//! AOT backend (`aot.rs`).

use std::path::Path;

use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};

use crate::{error::CompileError, solver::ConstrainedTree};

use super::compile::compile_elaborated;

/// Which machine `cantor build` is emitting code for.
///
/// Cantor's LLVM output is pointer-width agnostic by construction, which is
/// what makes a 32-bit target viable at all: every runtime handle crosses
/// the `extern "C"` boundary as a bare `i64` (see
/// `codegen::runtime_decls`), never as an LLVM pointer, and codegen never
/// converts an integer back into a pointer. The only pointer-to-integer
/// conversions are the diagnostic-message globals passed to the abort
/// helpers, and those zero-extend from `i32` on wasm32 just as they pass
/// through unchanged on x86-64.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildTarget {
    /// The host machine, using its exact CPU/feature set — equivalent to a
    /// `-C target-cpu=native` build.
    Native,
    /// `wasm32-unknown-unknown`, for the browser demo pipeline.
    Wasm32,
}

impl BuildTarget {
    /// The Rust/LLVM target triple, which doubles as the `--target` argument
    /// passed to `rustc` when linking the driver (`aot.rs`).
    pub fn triple(self) -> &'static str {
        match self {
            BuildTarget::Native => "",
            BuildTarget::Wasm32 => "wasm32-unknown-unknown",
        }
    }
}

/// Verify `module` and write it to `path` as an object file for `target`.
///
/// For `Wasm32` the module's triple and data layout are overwritten before
/// emission: codegen builds a module without either (so it defaults to the
/// host's), and `wasm-ld` rejects an object whose layout disagrees with the
/// rest of the link. Retroactively setting them is sound here only because
/// codegen never bakes in a pointer size — see `BuildTarget`'s doc comment.
pub fn write_object_file(
    module: &Module,
    path: &Path,
    target: BuildTarget,
) -> Result<(), CompileError> {
    module
        .verify()
        .map_err(|e| CompileError::ice(e.to_string()))?;

    let (triple, cpu, features) = match target {
        BuildTarget::Native => {
            Target::initialize_native(&InitializationConfig::default())
                .map_err(CompileError::ice)?;
            (
                TargetMachine::get_default_triple(),
                TargetMachine::get_host_cpu_name().to_string(),
                TargetMachine::get_host_cpu_features().to_string(),
            )
        }
        BuildTarget::Wasm32 => {
            Target::initialize_webassembly(&InitializationConfig::default());
            (
                TargetTriple::create(target.triple()),
                "generic".to_string(),
                String::new(),
            )
        }
    };

    let llvm_target = Target::from_triple(&triple).map_err(|e| CompileError::ice(e.to_string()))?;
    let target_machine = llvm_target
        .create_target_machine(
            &triple,
            &cpu,
            &features,
            OptimizationLevel::Default,
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or_else(|| {
            CompileError::ice(format!(
                "failed to create target machine for triple {}",
                triple.as_str().to_string_lossy()
            ))
        })?;

    if target == BuildTarget::Wasm32 {
        module.set_triple(&triple);
        module.set_data_layout(&target_machine.get_target_data().get_data_layout());
    }

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
    target: BuildTarget,
) -> Result<(), CompileError> {
    let compiler = compile_elaborated(
        ctx,
        &tree.items,
        &tree.sem_items,
        tree.overflow_checks.clone(),
        Some((path.to_string(), src.to_string())),
        tree.overload_resolution.clone(),
    )?;
    write_object_file(compiler.module(), out, target)
}
