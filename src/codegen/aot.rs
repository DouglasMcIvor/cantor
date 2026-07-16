//! `cantor build` — AOT compilation to a standalone executable.
//!
//! v0 scope is deliberately narrow: only the MVP IO event loop `main` shape
//! (`Char* * S -> Char* * S`, docs/design-decisions.md §6) is supported, by
//! explicit product decision — scalar/tuple `main` is JIT-only
//! (`cantor run`) and always will be, so there's no driver-generation logic
//! for those shapes here at all.
//!
//! Pipeline: emit the proved `ConstrainedTree` to a native object file
//! (`object::compile_constrained_to_object`), generate a tiny Rust "driver"
//! source that calls `cantor_runtime::event_loop::drive_event_loop` with the
//! program's statically-linked `cantor_initial_state`/`cantor_step` symbols,
//! then shell out to `rustc` to compile the driver and link it together with
//! the object file and the already-built `cantor-runtime` rlib.

use std::path::{Path, PathBuf};

use inkwell::context::Context;

use crate::{
    error::CompileError, kind::Kind, runtime::deep_copy::LeafShape, semantics::tree::SemItem,
    solver::ConstrainedTree, span::Span,
};

use super::{object::compile_constrained_to_object, wire};

/// Find the event-loop `main`'s State Kind, if `tree` defines one — `None`
/// means this file just isn't using the event-loop feature (an ordinary
/// zero-arg `main`, or none at all). Shared by `main.rs` (JIT dispatch) and
/// `cantor build`'s CLI gate (the caller decides what "not an event-loop
/// program" means for its own subcommand — `run` falls back to scalar
/// dispatch, `build` refuses outright). The `Span` is `main`'s own
/// definition span — used only to anchor `wire::state_leaf_shape`'s error
/// case, since State itself is just a named set with no more specific
/// sub-expression to blame.
pub fn find_event_loop_state_kind(tree: &ConstrainedTree) -> Option<(Kind, Span)> {
    tree.sem_items.iter().find_map(|item| match item {
        SemItem::FunctionDef(def)
            if def.name.0 == "main"
                && wire::is_event_loop_step_shape(&def.param_kinds, &def.return_kind) =>
        {
            let Kind::Tuple(elems) = &def.return_kind else {
                unreachable!("is_event_loop_step_shape already checked this is a Tuple");
            };
            Some((elems[1].clone(), def.span))
        }
        _ => None,
    })
}

/// Compile `tree` (already proved by `solver::check_file`, already
/// confirmed by the caller to have an event-loop `main`) into a standalone
/// executable at `output`. `state_kind`/`state_span` are
/// `find_event_loop_state_kind`'s result. `path`/`src` are only used for
/// overflow-abort diagnostics baked into the object file, same as
/// `jit.rs::compile_constrained`.
pub fn build_executable(
    tree: &ConstrainedTree,
    path: &str,
    src: &str,
    state_kind: &Kind,
    state_span: Span,
    output: &Path,
    keep_temps: bool,
) -> Result<(), CompileError> {
    let n_state_leaves = wire::leaf_count(state_kind);
    let state_shape = wire::state_leaf_shape(state_kind, state_span)?;

    let tmp_dir = unique_temp_dir();
    std::fs::create_dir_all(&tmp_dir).map_err(|e| {
        CompileError::ice(format!(
            "could not create temp build dir {}: {e}",
            tmp_dir.display()
        ))
    })?;

    let result = build_executable_in(
        &tmp_dir,
        tree,
        path,
        src,
        n_state_leaves,
        &state_shape,
        output,
    );

    if keep_temps {
        eprintln!(
            "note: --keep-temps: build artifacts left at {}",
            tmp_dir.display()
        );
    } else {
        let _ = std::fs::remove_dir_all(&tmp_dir);
    }

    result
}

fn build_executable_in(
    tmp_dir: &Path,
    tree: &ConstrainedTree,
    path: &str,
    src: &str,
    n_state_leaves: usize,
    state_shape: &LeafShape,
    output: &Path,
) -> Result<(), CompileError> {
    let obj_path = tmp_dir.join("program.o");
    let ctx = Context::create();
    compile_constrained_to_object(&ctx, tree, path, src, &obj_path)?;

    let driver_path = tmp_dir.join("driver.rs");
    std::fs::write(&driver_path, driver_source(n_state_leaves, state_shape)).map_err(|e| {
        CompileError::ice(format!("could not write {}: {e}", driver_path.display()))
    })?;

    let deps_dir = runtime_deps_dir()?;
    let rlib = find_runtime_rlib(&deps_dir)?;

    let status = std::process::Command::new("rustc")
        .arg("--edition")
        .arg("2024")
        .arg("-O")
        .arg(&driver_path)
        .arg("--extern")
        .arg(format!("cantor_runtime={}", rlib.display()))
        .arg("-L")
        .arg(&deps_dir)
        .arg("-C")
        .arg(format!("link-arg={}", obj_path.display()))
        .arg("-o")
        .arg(output)
        .status()
        .map_err(|e| {
            CompileError::ice(format!(
                "could not run `rustc` — is a Rust toolchain installed and on PATH? ({e})"
            ))
        })?;

    if !status.success() {
        return Err(CompileError::ice(format!(
            "linking the compiled program failed (rustc exited with {status})"
        )));
    }

    Ok(())
}

/// The Rust "driver" compiled and linked in per `cantor build` invocation:
/// just enough to name the program's statically-linked event-loop
/// trampolines and hand them, plus the arena deep-copy shape of `State`
/// (see the arena memory plan; `render_leaf_shape` below), to the one
/// shared, hand-written loop-driving function in `cantor-runtime`. Every
/// event-loop program's driver is this same template, parameterized only by
/// `n_state_leaves` and a literal `LeafShape` expression — no `Kind`-shape
/// *branching* is needed here (see module doc), since `render_leaf_shape`
/// already resolved every branch at `cantor build` time.
fn driver_source(n_state_leaves: usize, state_shape: &LeafShape) -> String {
    format!(
        "unsafe extern \"C\" {{\n\
        \x20   fn cantor_initial_state(out: *mut i64);\n\
        \x20   fn cantor_step(input: *mut i64, out: *mut i64);\n\
        }}\n\
        \n\
        fn main() {{\n\
        \x20   unsafe {{\n\
        \x20       cantor_runtime::event_loop::drive_event_loop(\n\
        \x20           cantor_initial_state,\n\
        \x20           cantor_step,\n\
        \x20           {n_state_leaves},\n\
        \x20           {},\n\
        \x20       );\n\
        \x20   }}\n\
        }}\n",
        render_leaf_shape(state_shape)
    )
}

/// Render a `LeafShape` as a literal Rust expression referencing
/// `cantor_runtime::deep_copy::*` by its fully-qualified path — the
/// generated `driver.rs` is compiled as a standalone crate (via `rustc
/// --extern cantor_runtime=...`), so it has no `use` of this compiler's own
/// modules to shorten the path with.
fn render_leaf_shape(shape: &LeafShape) -> String {
    match shape {
        LeafShape::Scalar => "cantor_runtime::deep_copy::LeafShape::Scalar".to_string(),
        LeafShape::TaggedInt => "cantor_runtime::deep_copy::LeafShape::TaggedInt".to_string(),
        LeafShape::Set(backing) => format!(
            "cantor_runtime::deep_copy::LeafShape::Set({})",
            render_set_backing(backing)
        ),
        LeafShape::Vector(elem) => format!(
            "cantor_runtime::deep_copy::LeafShape::Vector({})",
            render_vector_elem_shape(elem)
        ),
        LeafShape::Tuple(elems) => format!(
            "cantor_runtime::deep_copy::LeafShape::Tuple(vec![{}])",
            elems
                .iter()
                .map(render_leaf_shape)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn render_set_backing(backing: &crate::runtime::deep_copy::SetBacking) -> &'static str {
    use crate::runtime::deep_copy::SetBacking;
    match backing {
        SetBacking::TaggedInt => "cantor_runtime::deep_copy::SetBacking::TaggedInt",
        SetBacking::PlainInt => "cantor_runtime::deep_copy::SetBacking::PlainInt",
        SetBacking::PlainBool => "cantor_runtime::deep_copy::SetBacking::PlainBool",
    }
}

fn render_vector_elem_shape(shape: &crate::runtime::deep_copy::VectorElemShape) -> String {
    use crate::runtime::deep_copy::VectorElemShape;
    match shape {
        VectorElemShape::FlatScalar { bool_backed } => format!(
            "cantor_runtime::deep_copy::VectorElemShape::FlatScalar {{ bool_backed: {bool_backed} }}"
        ),
        VectorElemShape::Nested(inner) => format!(
            "cantor_runtime::deep_copy::VectorElemShape::Nested(Box::new({}))",
            render_vector_elem_shape(inner)
        ),
    }
}

fn unique_temp_dir() -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    std::env::temp_dir().join(format!("cantor-build-{}-{nanos}", std::process::id()))
}

/// The `deps/` directory sitting next to the currently-running `cantor`
/// binary (`target/{debug,release}/deps/`) — where cargo already put the
/// rlib for `cantor-runtime` and its own transitive dependencies, since
/// building `cantor` itself already built its `cantor-runtime` dependency.
fn runtime_deps_dir() -> Result<PathBuf, CompileError> {
    let exe = std::env::current_exe().map_err(|e| {
        CompileError::ice(format!("could not determine current executable path: {e}"))
    })?;
    let dir = exe
        .parent()
        .ok_or_else(|| CompileError::ice("current executable has no parent directory"))?;
    Ok(dir.join("deps"))
}

/// Find the most-recently-built `libcantor_runtime-*.rlib` in `deps_dir`.
///
/// TODO: this glob-and-pick-newest heuristic can pick a stale rlib if
/// `cantor-runtime`'s source changed without `cantor` itself being rebuilt
/// since (a normal `cargo build` always rebuilds both together, so this
/// only bites if someone runs `cargo build -p cantor-runtime` in isolation
/// and then reuses an old `cantor` binary). A `cargo build --message-format
/// =json` invocation would name the exact artifact robustly, at the cost of
/// a subprocess + JSON parsing per build — not worth it yet for a
/// prototype's local-only `cantor build`.
fn find_runtime_rlib(deps_dir: &Path) -> Result<PathBuf, CompileError> {
    let mut candidates: Vec<(std::time::SystemTime, PathBuf)> = std::fs::read_dir(deps_dir)
        .map_err(|e| {
            CompileError::ice(format!(
                "could not read {}: {e} — run `cargo build` first",
                deps_dir.display()
            ))
        })?
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("libcantor_runtime-") && n.ends_with(".rlib"))
        })
        .filter_map(|p| {
            std::fs::metadata(&p)
                .ok()
                .and_then(|m| m.modified().ok())
                .map(|t| (t, p))
        })
        .collect();

    candidates.sort_by_key(|(t, _)| *t);
    candidates.pop().map(|(_, p)| p).ok_or_else(|| {
        CompileError::ice(format!(
            "could not find a built cantor-runtime rlib in {} — run `cargo build` first",
            deps_dir.display()
        ))
    })
}
