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

use super::{
    object::{BuildTarget, compile_constrained_to_object},
    wire,
};

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
pub struct BuildRequest<'a> {
    pub tree: &'a ConstrainedTree,
    pub path: &'a str,
    pub src: &'a str,
    pub state_kind: &'a Kind,
    pub state_span: Span,
    pub output: &'a Path,
    pub keep_temps: bool,
    pub target: BuildTarget,
}

pub fn build_executable(req: &BuildRequest) -> Result<(), CompileError> {
    let n_state_leaves = wire::leaf_count(req.state_kind);
    let state_shape = wire::state_leaf_shape(req.state_kind, req.state_span)?;

    let tmp_dir = unique_temp_dir();
    std::fs::create_dir_all(&tmp_dir).map_err(|e| {
        CompileError::ice(format!(
            "could not create temp build dir {}: {e}",
            tmp_dir.display()
        ))
    })?;

    let result = build_executable_in(&tmp_dir, req, n_state_leaves, &state_shape);

    if req.keep_temps {
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
    req: &BuildRequest,
    n_state_leaves: usize,
    state_shape: &LeafShape,
) -> Result<(), CompileError> {
    let target = req.target;
    let obj_path = tmp_dir.join("program.o");
    let ctx = Context::create();
    compile_constrained_to_object(&ctx, req.tree, req.path, req.src, &obj_path, target)?;

    let driver_path = tmp_dir.join("driver.rs");
    let driver = match target {
        BuildTarget::Native => native_driver_source(n_state_leaves, state_shape),
        BuildTarget::Wasm32 => wasm_driver_source(n_state_leaves, state_shape),
    };
    std::fs::write(&driver_path, driver).map_err(|e| {
        CompileError::ice(format!("could not write {}: {e}", driver_path.display()))
    })?;

    let deps_dir = runtime_deps_dir(target)?;
    let rlib = find_runtime_rlib(&deps_dir, target)?;

    let mut cmd = std::process::Command::new("rustc");
    cmd.arg("--edition")
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
        .arg(req.output);

    if target == BuildTarget::Wasm32 {
        // A `cdylib` is what makes rustc link with `wasm-ld` and export the
        // driver's `#[unsafe(no_mangle)]` shims in the module's export table
        // — a plain bin would produce a `_start`-only module the JS host has
        // no way to call into.
        cmd.arg("--target")
            .arg(target.triple())
            .arg("--crate-type")
            .arg("cdylib");
        // cantor-runtime's transitive dependencies include proc macros
        // (arrow pulls in zerocopy_derive), and a proc macro always builds
        // for the *host* — cargo leaves those `.so`s in the native deps dir
        // even during a cross build, so resolving the rlib's dependency
        // graph needs both directories on the search path. The wasm one is
        // passed first so it wins for every crate that exists in both.
        cmd.arg("-L").arg(runtime_deps_dir(BuildTarget::Native)?);
        // A wasm module is downloaded before it runs, so its size is a
        // user-visible cost in a way a native binary's isn't: stripping
        // takes a release build of the parrot example from 2.5M to 670K.
        // The cost is that a trap's stack trace loses function names, which
        // is worth it for a target whose whole point is being served over
        // the network.
        cmd.arg("-C").arg("strip=symbols");
    }

    let status = cmd.status().map_err(|e| {
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
fn native_driver_source(n_state_leaves: usize, state_shape: &LeafShape) -> String {
    format!(
        "{TRAMPOLINE_DECLS}\n\
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

/// The `wasm32` counterpart of `native_driver_source`: instead of a `main`
/// that owns a stdin loop, a set of `#[unsafe(no_mangle)]` shims that land in
/// the wasm module's export table, so the JS host can own the loop and call
/// one `Event` in at a time. Each is a one-liner over
/// `cantor_runtime::wasm`, which holds the real logic — see that module's
/// doc comment for the calling sequence the host must follow.
fn wasm_driver_source(n_state_leaves: usize, state_shape: &LeafShape) -> String {
    format!(
        "{TRAMPOLINE_DECLS}\n\
        #[unsafe(no_mangle)]\n\
        pub extern \"C\" fn cantor_wasm_init() {{\n\
        \x20   unsafe {{\n\
        \x20       cantor_runtime::wasm::init(\n\
        \x20           cantor_initial_state,\n\
        \x20           cantor_step,\n\
        \x20           {n_state_leaves},\n\
        \x20           {},\n\
        \x20       );\n\
        \x20   }}\n\
        }}\n\
        \n\
        #[unsafe(no_mangle)]\n\
        pub extern \"C\" fn cantor_wasm_input_buffer(len: usize) -> *mut u8 {{\n\
        \x20   cantor_runtime::wasm::input_buffer(len)\n\
        }}\n\
        \n\
        #[unsafe(no_mangle)]\n\
        pub extern \"C\" fn cantor_wasm_step(len: usize) {{\n\
        \x20   cantor_runtime::wasm::step(len)\n\
        }}\n\
        \n\
        #[unsafe(no_mangle)]\n\
        pub extern \"C\" fn cantor_wasm_output_ptr() -> *const u8 {{\n\
        \x20   cantor_runtime::wasm::output_ptr()\n\
        }}\n\
        \n\
        #[unsafe(no_mangle)]\n\
        pub extern \"C\" fn cantor_wasm_output_len() -> usize {{\n\
        \x20   cantor_runtime::wasm::output_len()\n\
        }}\n",
        render_leaf_shape(state_shape)
    )
}

/// The two symbols every event-loop program's object file exports, named
/// identically by both driver templates.
const TRAMPOLINE_DECLS: &str = "unsafe extern \"C\" {\n\
    \x20   fn cantor_initial_state(out: *mut i64);\n\
    \x20   fn cantor_step(input: *mut i64, out: *mut i64);\n\
}\n";

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
fn runtime_deps_dir(target: BuildTarget) -> Result<PathBuf, CompileError> {
    let exe = std::env::current_exe().map_err(|e| {
        CompileError::ice(format!("could not determine current executable path: {e}"))
    })?;
    let profile_dir = exe
        .parent()
        .ok_or_else(|| CompileError::ice("current executable has no parent directory"))?;

    match target {
        BuildTarget::Native => Ok(profile_dir.join("deps")),
        // Cargo puts cross-compiled artifacts under a per-triple directory
        // one level up: `target/{profile}/` becomes
        // `target/{triple}/{profile}/`.
        BuildTarget::Wasm32 => {
            let profile = profile_dir.file_name().ok_or_else(|| {
                CompileError::ice("current executable's directory has no final component")
            })?;
            let target_dir = profile_dir
                .parent()
                .ok_or_else(|| CompileError::ice("current executable's directory has no parent"))?;
            Ok(target_dir.join(target.triple()).join(profile).join("deps"))
        }
    }
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
fn find_runtime_rlib(deps_dir: &Path, target: BuildTarget) -> Result<PathBuf, CompileError> {
    // A plain `cargo build` only produces the host rlib, so a wasm build's
    // missing artifact is a routine "you haven't run the prerequisite
    // command yet", not a broken compiler — say exactly what to run.
    let missing = || match target {
        BuildTarget::Native => CompileError::ice(format!(
            "could not find a built cantor-runtime rlib in {} — run `cargo build` first",
            deps_dir.display()
        )),
        BuildTarget::Wasm32 => CompileError::Environment {
            detail: format!(
                "no wasm32 build of cantor-runtime found in {} — run `cargo build -p \
                 cantor-runtime --target {}` first (and `rustup target add {}` if you \
                 haven't already)",
                deps_dir.display(),
                target.triple(),
                target.triple(),
            ),
        },
    };

    let Ok(entries) = std::fs::read_dir(deps_dir) else {
        return Err(missing());
    };

    let mut candidates: Vec<(std::time::SystemTime, PathBuf)> = entries
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
    candidates.pop().map(|(_, p)| p).ok_or_else(missing)
}
