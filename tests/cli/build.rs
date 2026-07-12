//! `cantor build` end to end (docs/design-decisions.md §6's AOT backend) —
//! compiles a fixture to a standalone executable and runs *that binary*
//! directly (not through the `cantor` CLI), asserting its behavior matches
//! `cantor run`'s JIT output for the same fixture/stdin (see
//! tests/cli/event_loop.rs's equivalent JIT-path assertions).

use std::io::Write as _;
use std::process::{Command, Stdio};

use super::helpers::*;

/// Build `fixture_name` to a uniquely-named path under `target/` and return
/// the CLI's own `Output` plus the compiled binary's path. `label` only
/// needs to be unique within this file (tests in one binary run in
/// parallel). Deliberately *not* `std::env::temp_dir()` — some sandboxes
/// (this dev container included) mount `/tmp` `noexec`, which would make
/// every compiled test binary unrunnable through no fault of `cantor
/// build` itself; `target/` is always on the same executable filesystem
/// cargo already builds and runs test binaries from.
fn build_fixture(fixture_name: &str, label: &str) -> (Output, std::path::PathBuf) {
    let out_dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli-build-test-tmp");
    std::fs::create_dir_all(&out_dir).expect("failed to create test output dir");
    let out_path = out_dir.join(format!("{label}-{}", std::process::id()));
    let path = fixture(fixture_name);
    let out = run(&[
        "build",
        path.to_str().unwrap(),
        "-o",
        out_path.to_str().unwrap(),
    ]);
    (out, out_path)
}

/// Run an already-compiled binary directly, piping `input` to its stdin —
/// the AOT equivalent of `helpers::run_subcommand_with_stdin`.
fn run_compiled_with_stdin(bin: &std::path::Path, input: &str) -> Output {
    let mut cmd = Command::new(bin);
    cmd.stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = cmd
        .spawn()
        .unwrap_or_else(|e| panic!("failed to spawn compiled binary {}: {e}", bin.display()));
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");
    drop(child.stdin.take());
    let out = child
        .wait_with_output()
        .expect("failed to wait for compiled binary");
    Output {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code().unwrap_or(-1),
    }
}

/// Like `run_compiled_with_stdin`, but closes stdin immediately (no lines
/// piped) — an immediate-EOF run, mirroring `helpers::run_subcommand`.
fn run_compiled(bin: &std::path::Path) -> Output {
    run_compiled_with_stdin(bin, "")
}

#[test]
fn build_echoes_lines_with_persisted_state_matching_jit() {
    let (build_out, bin) = build_fixture("event_loop_echo.cantor", "echo-lines");
    assert_eq!(
        build_out.code, 0,
        "expected build to succeed\nstdout: {}\nstderr: {}",
        build_out.stdout, build_out.stderr
    );

    let out = run_compiled_with_stdin(&bin, "a\nb\nc\n");
    std::fs::remove_file(&bin).ok();

    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    // Same fixture/input as event_loop.rs's JIT test — same expected output.
    assert!(
        out.stdout.contains("a:0\nb:1\nc:2\n"),
        "expected echoed lines with a persisted counter:\n{}",
        out.stdout
    );
    let lines: Vec<&str> = out.stdout.lines().collect();
    assert!(
        lines.last().unwrap().ends_with(":3"),
        "expected one extra line for the EOT-triggered final call:\n{}",
        out.stdout
    );
}

#[test]
fn build_runs_once_for_eot_on_immediate_eof() {
    let (build_out, bin) = build_fixture("event_loop_echo.cantor", "immediate-eof");
    assert_eq!(build_out.code, 0, "expected build to succeed");

    let out = run_compiled(&bin);
    std::fs::remove_file(&bin).ok();

    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    let lines: Vec<&str> = out.stdout.lines().collect();
    assert!(
        lines.last().unwrap().ends_with(":0"),
        "expected exactly one EOT-triggered call against the seeded state:\n{}",
        out.stdout
    );
}

#[test]
fn build_refuses_non_event_loop_main() {
    // good.cantor has scalar mains only — cantor build's permanent scope
    // boundary (scalar/tuple main is JIT-only), not an "unimplemented" gap.
    let (out, bin) = build_fixture("good.cantor", "scalar-main");
    assert_ne!(
        out.code, 0,
        "should refuse to build:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("event-loop") && out.stderr.contains("cantor run"),
        "expected the event-loop-only scope diagnostic:\n{}",
        out.stderr
    );
    assert!(!bin.exists(), "no executable should have been written");
}

#[test]
fn build_refuses_when_counterexample_found() {
    let (out, bin) = build_fixture("event_loop_bad.cantor", "counterexample");
    assert_ne!(
        out.code, 0,
        "should refuse to build:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("not building"),
        "expected refusal message on stderr:\n{}",
        out.stderr
    );
    assert!(!bin.exists(), "no executable should have been written");
}

#[test]
fn build_produces_no_cvc5_or_llvm_dependency() {
    // The whole point of the cantor-runtime crate split: a compiled Cantor
    // executable should not need libcvc5/libLLVM at runtime.
    let (build_out, bin) = build_fixture("event_loop_echo.cantor", "ldd-check");
    assert_eq!(build_out.code, 0, "expected build to succeed");

    let ldd = Command::new("ldd")
        .arg(&bin)
        .output()
        .expect("failed to run ldd");
    std::fs::remove_file(&bin).ok();

    let deps = String::from_utf8_lossy(&ldd.stdout);
    assert!(
        !deps.to_lowercase().contains("cvc5") && !deps.to_lowercase().contains("libllvm"),
        "compiled executable should not depend on cvc5/LLVM:\n{}",
        deps
    );
}

#[test]
fn parrot_builds_and_echoes_matching_jit() {
    // The user's own motivating example for this feature.
    let (build_out, bin) = build_fixture("parrot.cantor", "parrot");
    assert_eq!(
        build_out.code, 0,
        "expected build to succeed\nstdout: {}\nstderr: {}",
        build_out.stdout, build_out.stderr
    );

    let out = run_compiled_with_stdin(&bin, "hi\n");
    std::fs::remove_file(&bin).ok();

    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("hi hi\n"),
        "expected the first call to echo `text` doubled (n starts at 1):\n{}",
        out.stdout
    );
}
