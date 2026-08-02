//! `cantor build --target wasm32` end to end — the browser demo pipeline
//! (docs/design-decisions.md §6). The wasm *object emission* is covered
//! unconditionally in tests/codegen/object.rs, since LLVM does that on its
//! own; what needs a real toolchain, and so is tested here, is the link:
//! producing a module whose export table carries the host ABI
//! `cantor-runtime/src/wasm.rs` defines.

use super::helpers::*;

/// The contract between `codegen::aot::wasm_driver_source` (which defines
/// them), `cantor-runtime/src/wasm.rs` (which implements them) and
/// `web/cantor.js` (which calls them).
const HOST_ABI_EXPORTS: [&str; 5] = [
    "cantor_wasm_init",
    "cantor_wasm_input_buffer",
    "cantor_wasm_step",
    "cantor_wasm_output_ptr",
    "cantor_wasm_output_len",
];

/// The Image-Output counterpart of `HOST_ABI_EXPORTS` — `wasm_driver_source`
/// emits exactly one of these two export sets per module, never both (see
/// that function's doc comment), so an Image-Output module's export table
/// has these instead of `cantor_wasm_output_ptr`/`_len`.
const IMAGE_OUTPUT_ABI_EXPORTS: [&str; 4] = [
    "cantor_wasm_output_width",
    "cantor_wasm_output_height",
    "cantor_wasm_output_pixels_ptr",
    "cantor_wasm_output_pixels_len",
];

/// Linking a wasm module needs two things `cargo test` does not itself
/// provide: the `wasm32-unknown-unknown` rust-std, and a cross-compiled
/// `cantor-runtime` rlib (`cargo build -p cantor-runtime --target
/// wasm32-unknown-unknown`). Returns the deps directory when it's there.
fn wasm_runtime_deps_dir() -> Option<std::path::PathBuf> {
    // Mirrors codegen::aot::runtime_deps_dir — the test binary lives in
    // target/{profile}/deps/, one level deeper than the cantor binary.
    let exe = std::env::current_exe().ok()?;
    let profile_dir = exe.parent()?.parent()?;
    let profile = profile_dir.file_name()?;
    let dir = profile_dir
        .parent()?
        .join("wasm32-unknown-unknown")
        .join(profile)
        .join("deps");

    let has_rlib = std::fs::read_dir(&dir)
        .ok()?
        .filter_map(|e| e.ok())
        .any(|e| {
            e.file_name()
                .to_str()
                .is_some_and(|n| n.starts_with("libcantor_runtime-") && n.ends_with(".rlib"))
        });
    has_rlib.then_some(dir)
}

fn build_wasm_fixture(fixture_name: &str, label: &str) -> (Output, std::path::PathBuf) {
    let out_dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli-build-test-tmp");
    std::fs::create_dir_all(&out_dir).expect("failed to create test output dir");
    let out_path = out_dir.join(format!("{label}-{}.wasm", std::process::id()));
    let path = fixture(fixture_name);
    let out = run(&[
        "build",
        "--target",
        "wasm32",
        path.to_str().unwrap(),
        "-o",
        out_path.to_str().unwrap(),
    ]);
    (out, out_path)
}

#[test]
fn build_wasm_emits_a_module_exporting_the_host_abi() {
    let Some(_deps) = wasm_runtime_deps_dir() else {
        eprintln!(
            "SKIPPED build_wasm_emits_a_module_exporting_the_host_abi: no wasm32 \
             cantor-runtime rlib — run `rustup target add wasm32-unknown-unknown && \
             cargo build -p cantor-runtime --target wasm32-unknown-unknown`"
        );
        return;
    };

    let (build_out, module) = build_wasm_fixture("parrot.cantor", "wasm-parrot");
    assert_eq!(
        build_out.code, 0,
        "expected build to succeed\nstdout: {}\nstderr: {}",
        build_out.stdout, build_out.stderr
    );
    assert!(
        build_out.stdout.contains("wrote wasm module"),
        "expected the wasm-specific success line:\n{}",
        build_out.stdout
    );

    let bytes = std::fs::read(&module).expect("wasm module should have been written");
    std::fs::remove_file(&module).ok();

    assert_eq!(&bytes[0..4], b"\0asm", "expected a wasm module");

    // The export names are the host ABI contract cantor.js codes against —
    // they appear literally in the module's export section, so a plain byte
    // search is enough to catch the driver template drifting from the shim.
    for symbol in HOST_ABI_EXPORTS {
        assert!(
            bytes.windows(symbol.len()).any(|w| w == symbol.as_bytes()),
            "expected the module to export `{symbol}`"
        );
    }
}

#[test]
fn build_wasm_image_output_produces_a_module() {
    let Some(_deps) = wasm_runtime_deps_dir() else {
        eprintln!(
            "SKIPPED build_wasm_image_output_produces_a_module: no wasm32 cantor-runtime \
             rlib — run `rustup target add wasm32-unknown-unknown && cargo build -p \
             cantor-runtime --target wasm32-unknown-unknown`"
        );
        return;
    };

    // Unlike native `cantor build`/`cantor run` (see tests/cli/build.rs's
    // `build_refuses_image_output_for_native_target` and
    // tests/cli/event_loop.rs's `image_output_run_refuses_cleanly`), the
    // wasm32 target actually builds an Image-Output event-loop program —
    // this is the one place `wasm_driver_source`'s Image branch is
    // exercised end to end.
    let (build_out, module) =
        build_wasm_fixture("event_loop_image_output.cantor", "wasm-image-output");
    assert_eq!(
        build_out.code, 0,
        "expected build to succeed\nstdout: {}\nstderr: {}",
        build_out.stdout, build_out.stderr
    );

    let bytes = std::fs::read(&module).expect("wasm module should have been written");
    std::fs::remove_file(&module).ok();

    assert_eq!(&bytes[0..4], b"\0asm", "expected a wasm module");

    for symbol in [
        "cantor_wasm_init",
        "cantor_wasm_input_buffer",
        "cantor_wasm_step",
    ] {
        assert!(
            bytes.windows(symbol.len()).any(|w| w == symbol.as_bytes()),
            "expected the module to export `{symbol}`"
        );
    }
    for symbol in IMAGE_OUTPUT_ABI_EXPORTS {
        assert!(
            bytes.windows(symbol.len()).any(|w| w == symbol.as_bytes()),
            "expected the module to export the Image-Output accessor `{symbol}`"
        );
    }
    // The Char*-Output accessors must NOT appear — `wasm_driver_source`
    // emits exactly one export set per module (see IMAGE_OUTPUT_ABI_EXPORTS'
    // doc comment), and a stray `cantor_wasm_output_ptr` export would be a
    // real ABI-generation bug (a JS host could call it and read garbage,
    // since cantor-runtime's `output_ptr` panics on the wrong OutputValue
    // variant only at *call* time, not at export-table-inspection time).
    for symbol in ["cantor_wasm_output_ptr", "cantor_wasm_output_len"] {
        assert!(
            !bytes.windows(symbol.len()).any(|w| w == symbol.as_bytes()),
            "did not expect the module to export the Char*-Output accessor `{symbol}`"
        );
    }
}

#[test]
fn build_wasm_reports_a_missing_runtime_as_environment_not_ice() {
    if wasm_runtime_deps_dir().is_some() {
        // The prerequisite is present, so this failure mode can't be
        // provoked without deleting another test's build artifacts.
        return;
    }

    let (out, module) = build_wasm_fixture("parrot.cantor", "wasm-missing-runtime");
    assert_ne!(out.code, 0, "expected the build to fail");
    assert!(
        !out.stderr.contains("internal compiler error"),
        "a missing cross-compiled runtime is a fixable environment problem, \
         not a compiler bug:\n{}",
        out.stderr
    );
    assert!(
        out.stderr.contains("cargo build -p cantor-runtime"),
        "expected the error to name the command that fixes it:\n{}",
        out.stderr
    );
    assert!(!module.exists(), "no module should have been written");
}

/// A minimal Node.js host script that drives one `cantor_wasm_step` call
/// against an Image-Output module and prints `width`/`height` as the only
/// two lines of stdout — just enough to check the decoded dimensions
/// without pulling in the pixel buffer too.
const NODE_IMAGE_DIMENSIONS_SCRIPT: &str = r#"
import fs from "node:fs";
const bytes = fs.readFileSync(process.argv[2]);
const { instance } = await WebAssembly.instantiate(bytes, {});
const exports = instance.exports;
exports.cantor_wasm_init();
exports.cantor_wasm_input_buffer(0);
exports.cantor_wasm_step(0);
console.log(exports.cantor_wasm_output_width());
console.log(exports.cantor_wasm_output_height());
"#;

/// Returns `true` if a `node` binary is on `PATH` — Node.js isn't a Rust
/// build dependency, so this test degrades to a skip (mirroring
/// `wasm_runtime_deps_dir`'s pattern) rather than a hard failure on a
/// machine that never installed it.
fn node_available() -> bool {
    std::process::Command::new("node")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

#[test]
fn build_wasm_image_output_decodes_correct_dimensions() {
    let Some(_deps) = wasm_runtime_deps_dir() else {
        eprintln!(
            "SKIPPED build_wasm_image_output_decodes_correct_dimensions: no wasm32 \
             cantor-runtime rlib — run `rustup target add wasm32-unknown-unknown && \
             cargo build -p cantor-runtime --target wasm32-unknown-unknown`"
        );
        return;
    };
    if !node_available() {
        eprintln!("SKIPPED build_wasm_image_output_decodes_correct_dimensions: no `node` on PATH");
        return;
    }

    // Regression test for the Int64→Int re-tagging gap (tests/cli/
    // int64_retag.rs has the minimal non-wasm repros): `width`/`height` are
    // 0-arity `Nat`-returning functions, both Step-A-promoted to raw
    // `Kind::Int64` — before the fix, their values reached the wasm host
    // untagged and `cantor-runtime::event_loop::decode_output` silently
    // halved them (10, 7 became 5, 3).
    let (build_out, module) = build_wasm_fixture(
        "int64_retag_event_loop_image.cantor",
        "wasm-image-dimensions",
    );
    assert_eq!(
        build_out.code, 0,
        "expected build to succeed\nstdout: {}\nstderr: {}",
        build_out.stdout, build_out.stderr
    );

    let script_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target/cli-build-test-tmp")
        .join(format!("image-dimensions-{}.mjs", std::process::id()));
    std::fs::write(&script_path, NODE_IMAGE_DIMENSIONS_SCRIPT)
        .expect("failed to write the node test script");

    let node_out = std::process::Command::new("node")
        .arg(&script_path)
        .arg(&module)
        .output()
        .expect("failed to run node");
    std::fs::remove_file(&script_path).ok();
    std::fs::remove_file(&module).ok();

    assert!(
        node_out.status.success(),
        "expected node to exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&node_out.stdout),
        String::from_utf8_lossy(&node_out.stderr)
    );
    let stdout = String::from_utf8_lossy(&node_out.stdout);
    let mut lines = stdout.lines();
    assert_eq!(
        lines.next(),
        Some("10"),
        "expected width() = 10, correctly tagged:\n{stdout}"
    );
    assert_eq!(
        lines.next(),
        Some("7"),
        "expected height() = 7, correctly tagged:\n{stdout}"
    );
}

/// A Node.js host script that drives one `cantor_wasm_step` call against the
/// Game of Life demo and prints the decoded pixel buffer as one `#`/`.` row
/// per pixel row (thresholding each pixel's red channel, since the demo
/// packs pure black/white — `0xFFFFFFFF`/`0x000000FF` — one `Unsigned32` per
/// pixel).
const NODE_GAME_OF_LIFE_ASCII_SCRIPT: &str = r##"
import fs from "node:fs";
const bytes = fs.readFileSync(process.argv[2]);
const { instance } = await WebAssembly.instantiate(bytes, {});
const exports = instance.exports;
exports.cantor_wasm_init();
exports.cantor_wasm_input_buffer(0);
exports.cantor_wasm_step(0);
const width = exports.cantor_wasm_output_width();
const height = exports.cantor_wasm_output_height();
const ptr = exports.cantor_wasm_output_pixels_ptr();
const len = exports.cantor_wasm_output_pixels_len();
const mem = new Uint8Array(exports.memory.buffer, ptr, len * 4);
let rows = [];
for (let y = 0; y < height; y++) {
    let row = "";
    for (let x = 0; x < width; x++) {
        row += mem[(y * width + x) * 4] > 128 ? "#" : ".";
    }
    rows.push(row);
}
console.log(rows.join("\n"));
"##;

#[test]
fn build_wasm_game_of_life_evolves_the_glider_one_generation() {
    let Some(_deps) = wasm_runtime_deps_dir() else {
        eprintln!(
            "SKIPPED build_wasm_game_of_life_evolves_the_glider_one_generation: no wasm32 \
             cantor-runtime rlib — run `rustup target add wasm32-unknown-unknown && \
             cargo build -p cantor-runtime --target wasm32-unknown-unknown`"
        );
        return;
    };
    if !node_available() {
        eprintln!(
            "SKIPPED build_wasm_game_of_life_evolves_the_glider_one_generation: no `node` on PATH"
        );
        return;
    }

    // examples/game_of_life.cantor lives outside tests/cantor_files (it's a
    // real user-facing demo, not a test fixture) — build it directly rather
    // than through `build_wasm_fixture`/`fixture`.
    let example_path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/game_of_life.cantor");
    let out_dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli-build-test-tmp");
    std::fs::create_dir_all(&out_dir).expect("failed to create test output dir");
    let module = out_dir.join(format!("game-of-life-{}.wasm", std::process::id()));
    let build_out = run(&[
        "build",
        "--target",
        "wasm32",
        example_path.to_str().unwrap(),
        "-o",
        module.to_str().unwrap(),
    ]);
    assert_eq!(
        build_out.code, 0,
        "expected build to succeed\nstdout: {}\nstderr: {}",
        build_out.stdout, build_out.stderr
    );

    let script_path = out_dir.join(format!("game-of-life-{}.mjs", std::process::id()));
    std::fs::write(&script_path, NODE_GAME_OF_LIFE_ASCII_SCRIPT)
        .expect("failed to write the node test script");

    let node_out = std::process::Command::new("node")
        .arg(&script_path)
        .arg(&module)
        .output()
        .expect("failed to run node");
    std::fs::remove_file(&script_path).ok();
    std::fs::remove_file(&module).ok();

    assert!(
        node_out.status.success(),
        "expected node to exit 0\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&node_out.stdout),
        String::from_utf8_lossy(&node_out.stderr)
    );

    // The demo seeds a glider (docs/design-decisions.md's canonical `.#.` /
    // `..#` / `###` shape) in the top-left corner of a 30x30 torus; one
    // generation forward under the standard B3/S23 rule is the well-known
    // `#.#` / `.##` / `.#.` phase, shifted down by one row from the seed —
    // far enough from every edge that the torus wrap doesn't kick in yet
    // after a single generation. This is a real regression test for the
    // Int64 re-tagging fix (tests/cli/int64_retag.rs) in its actual
    // motivating context — a wrong width/height here would misalign every
    // row.
    let expected = "\
..............................
#.#...........................
.##...........................
.#............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................
..............................";
    let stdout = String::from_utf8_lossy(&node_out.stdout);
    assert_eq!(
        stdout.trim_end(),
        expected,
        "expected the glider's known one-generation-forward shape:\n{stdout}"
    );
}

/// The browser shim is JavaScript, so nothing in `cargo test` type-checks it
/// against the driver template that produces the exports it calls. This
/// keeps the two from drifting silently: every symbol the module is required
/// to export above must actually be named somewhere in `web/cantor.js`.
#[test]
fn the_browser_shim_uses_the_exported_host_abi() {
    let shim_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("web/cantor.js");
    let shim = std::fs::read_to_string(&shim_path)
        .unwrap_or_else(|e| panic!("could not read {}: {e}", shim_path.display()));

    for symbol in HOST_ABI_EXPORTS {
        assert!(
            shim.contains(symbol),
            "web/cantor.js never calls `{symbol}` — the shim and the wasm driver \
             template (codegen::aot::wasm_driver_source) have drifted apart"
        );
    }
}

#[test]
fn build_wasm_rejects_an_unknown_target() {
    let out = run(&[
        "build",
        "--target",
        "risc-v-toaster",
        fixture("parrot.cantor").to_str().unwrap(),
    ]);
    assert_eq!(out.code, 2, "expected a usage-error exit code");
    assert!(
        out.stderr.contains("unknown --target"),
        "expected an unknown-target diagnostic:\n{}",
        out.stderr
    );
}
