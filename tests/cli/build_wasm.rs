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

/// The demo pages display the program they run by fetching it at load time,
/// so `web/<demo>.cantor` is a symlink to the real `examples/<demo>.cantor`
/// rather than a second copy. That is exactly the drift this guards: the
/// pages previously pasted the source into their HTML, and the Game of Life
/// copy was already several functions out of date by the time anyone noticed.
/// A broken symlink, or someone "helpfully" replacing one with a plain file,
/// fails here rather than quietly on the deployed page.
#[test]
fn the_demo_pages_serve_the_real_example_sources() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    for (page, program) in [
        ("web/index.html", "parrot.cantor"),
        ("web/game-of-life.html", "game_of_life.cantor"),
        ("web/paper-bag.html", "quantum_paper_bag.cantor"),
    ] {
        let served = root.join("web").join(program);
        let original = root.join("examples").join(program);
        let served_text = std::fs::read_to_string(&served)
            .unwrap_or_else(|e| panic!("could not read {}: {e}", served.display()));
        let original_text = std::fs::read_to_string(&original)
            .unwrap_or_else(|e| panic!("could not read {}: {e}", original.display()));
        assert_eq!(
            served_text,
            original_text,
            "{} has drifted from {} — it is meant to be a symlink to it, not a copy",
            served.display(),
            original.display()
        );

        let html = std::fs::read_to_string(root.join(page))
            .unwrap_or_else(|e| panic!("could not read {page}: {e}"));
        assert!(
            html.contains(&format!(
                "showProgramSource(document.getElementById(\"source\"), \"./{program}\")"
            )),
            "{page} no longer fetches ./{program} to display — the page and \
             web/cantor.js's showProgramSource have drifted apart"
        );
        // A signature line is the unmistakable fingerprint of Cantor source
        // pasted into the HTML; prose mentioning `<code>main</code>` is fine.
        assert!(
            !html.contains("main :"),
            "{page} looks like it has an inlined copy of the program again — \
             it should fetch ./{program} instead, so it cannot go stale"
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

/// A Node host that runs the paper-bag demo far enough to be interesting and
/// prints three facts about the result: the image dimensions, whether the
/// banner strip is dark before any measurement, and whether measuring
/// repeatedly eventually lights it (the escape).
const NODE_PAPER_BAG_SCRIPT: &str = r##"
import fs from "node:fs";
const bytes = fs.readFileSync(process.argv[2]);
const { instance } = await WebAssembly.instantiate(bytes, {});
const ex = instance.exports;
ex.cantor_wasm_init();
const enc = new TextEncoder();
function step(s) {
    const b = enc.encode(s);
    const p = ex.cantor_wasm_input_buffer(b.length);
    new Uint8Array(ex.memory.buffer).set(b, p);
    ex.cantor_wasm_step(b.length);
    const w = ex.cantor_wasm_output_width(), h = ex.cantor_wasm_output_height();
    const pp = ex.cantor_wasm_output_pixels_ptr(), pl = ex.cantor_wasm_output_pixels_len();
    return { w, h, m: new Uint8Array(ex.memory.buffer.slice(pp, pp + pl)) };
}
// The strip below the grid always carries the live escape chance, drawn in
// a muted blue-grey; only the ESCAPED banner is green. So the escape signal
// is the colour, not merely a lit pixel.
function escapeLit(f) {
    for (let y = f.w; y < f.h; y++)
        for (let x = 0; x < f.w; x++) {
            const o = (y * f.w + x) * 4;
            const r = f.m[o], g = f.m[o + 1], b = f.m[o + 2];
            if (g > 180 && r < 140 && b > 100 && b < 200) return true;
        }
    return false;
}
// Any lit pixel at all — the percentage readout should be there from the
// very first frame.
function anyLit(f) {
    for (let y = f.w; y < f.h; y++)
        for (let x = 0; x < f.w; x++) {
            const o = (y * f.w + x) * 4;
            if (f.m[o] + f.m[o + 1] + f.m[o + 2] > 120) return true;
        }
    return false;
}
let f = step("");
console.log(`dims ${f.w}x${f.h}`);
console.log(`banner-before ${escapeLit(f)}`);
console.log(`readout ${anyLit(f)}`);
// The Event protocol is carried by length alone: empty ticks, non-empty
// measures. Deterministic lengths here — the program's own LCG supplies the
// variation, so the test does not depend on Math.random and this sequence
// escapes on measurement 2 every time. The loop bound is only a safety net,
// and is kept low because each step is real work (~16ms at 32x32).
let escaped = false;
for (let k = 1; k <= 20 && !escaped; k++) {
    for (let i = 0; i < 150; i++) f = step("");
    f = step("x".repeat(1 + ((k * 977) % 4093)));
    escaped = escapeLit(f);
}
console.log(`banner-after ${escaped}`);
"##;

/// The paper-bag demo end to end: it is the only program that exercises a
/// multi-vector tuple `State` across the wasm event loop, and the only one
/// whose Image is taller than it is wide (the grid plus the banner strip
/// that "ESCAPED" is drawn into). Both of those were codegen bugs during
/// development, so this pins them.
#[test]
fn build_wasm_paper_bag_tunnels_out_and_lights_the_banner() {
    let Some(_deps) = wasm_runtime_deps_dir() else {
        eprintln!(
            "SKIPPED build_wasm_paper_bag_tunnels_out_and_lights_the_banner: no wasm32 \
             cantor-runtime rlib — run `rustup target add wasm32-unknown-unknown && \
             cargo build -p cantor-runtime --target wasm32-unknown-unknown`"
        );
        return;
    };
    if !node_available() {
        eprintln!(
            "SKIPPED build_wasm_paper_bag_tunnels_out_and_lights_the_banner: no `node` on PATH"
        );
        return;
    }

    let example_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/quantum_paper_bag.cantor");
    let out_dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli-build-test-tmp");
    std::fs::create_dir_all(&out_dir).expect("failed to create test output dir");
    let module = out_dir.join(format!("paper-bag-{}.wasm", std::process::id()));
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

    let script_path = out_dir.join(format!("paper-bag-{}.mjs", std::process::id()));
    std::fs::write(&script_path, NODE_PAPER_BAG_SCRIPT)
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

    // 32-wide grid plus the 8-row banner strip.
    assert!(
        stdout.contains("dims 32x40"),
        "expected a 32x40 image (grid plus banner strip), got:\n{stdout}"
    );
    assert!(
        stdout.contains("banner-before false"),
        "the ESCAPED banner must not be lit before any measurement, got:\n{stdout}"
    );
    assert!(
        stdout.contains("readout true"),
        "the escape-chance readout should occupy the banner strip from the \
         first frame, got:\n{stdout}"
    );
    assert!(
        stdout.contains("banner-after true"),
        "expected the particle to tunnel out and light the ESCAPED banner \
         within 20 measurements, got:\n{stdout}"
    );
}
