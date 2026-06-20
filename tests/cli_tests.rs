//! Integration tests for the `cantor` CLI binary.
//!
//! These tests run the compiled binary as a subprocess and check its exit
//! codes, stdout, and stderr. They live alongside the `.cantor` fixture files
//! in `tests/cantor_files/` so that both evolve together as the CLI grows.

use std::path::PathBuf;
use std::process::Command;

// ── Helpers ───────────────────────────────────────────────────────────────────

fn cantor() -> Command {
    Command::new(env!("CARGO_BIN_EXE_cantor"))
}

fn fixture(name: &str) -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("tests/cantor_files");
    p.push(name);
    p
}

struct Output {
    stdout: String,
    stderr: String,
    code: i32,
}

fn run(args: &[&str]) -> Output {
    let mut cmd = cantor();
    for &a in args {
        cmd.arg(a);
    }
    let out = cmd.output().expect("failed to spawn cantor binary");
    Output {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code:   out.status.code().unwrap_or(-1),
    }
}

fn run_file(name: &str) -> Output {
    let path = fixture(name);
    run(&[path.to_str().unwrap()])
}

fn run_subcommand(name: &str) -> Output {
    let path = fixture(name);
    run(&["run", path.to_str().unwrap()])
}

// ── No-arg / usage ────────────────────────────────────────────────────────────

#[test]
fn no_args_prints_usage_and_exits_2() {
    let out = run(&[]);
    assert_eq!(out.code, 2, "expected exit 2 for missing argument");
    assert!(
        out.stderr.contains("usage"),
        "expected usage hint on stderr, got: {:?}", out.stderr
    );
}

// ── Missing file ──────────────────────────────────────────────────────────────

#[test]
fn missing_file_exits_nonzero() {
    let out = run(&["/nonexistent/cantor_file.cantor"]);
    assert_ne!(out.code, 0, "expected non-zero exit for missing file");
    assert!(!out.stderr.is_empty(), "expected error message on stderr");
}

// ── Parse errors ──────────────────────────────────────────────────────────────

#[test]
fn parse_error_exits_nonzero() {
    let out = run_file("parse_error.cantor");
    assert_ne!(out.code, 0, "expected non-zero exit for parse error");
}

#[test]
fn parse_error_message_goes_to_stderr() {
    let out = run_file("parse_error.cantor");
    assert!(
        !out.stderr.is_empty(),
        "expected parse error on stderr, stdout was: {:?}", out.stdout
    );
}

// ── Good file: all proved ─────────────────────────────────────────────────────

#[test]
fn good_file_exits_zero() {
    let out = run_file("good.cantor");
    assert_eq!(out.code, 0, "good.cantor should exit 0\nstdout: {}", out.stdout);
}

#[test]
fn good_file_reports_proved_for_every_function() {
    let out = run_file("good.cantor");
    // abs, double, quad — all should be proved.
    for name in &["abs", "double", "quad"] {
        assert!(
            out.stdout.contains(name),
            "expected `{name}` in output:\n{}", out.stdout
        );
    }
    // Match the indented result-line prefix, not just the bare word
    // (the summary "0 counterexample(s)" also contains "counterexample").
    assert!(
        out.stdout.contains("  proved  "),
        "expected '  proved  ' result line in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample result line in output:\n{}", out.stdout
    );
}

#[test]
fn good_file_summary_line() {
    let out = run_file("good.cantor");
    // Summary should show 3 proved and no failures.
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("0 counterexample"),
        "expected '0 counterexample' in summary:\n{}", out.stdout
    );
}

#[test]
fn good_file_shows_signatures() {
    // The signature of each function should appear in the output.
    let out = run_file("good.cantor");
    assert!(out.stdout.contains("Int -> Nat"),  "abs sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("Nat -> Nat"),  "double/quad sig missing:\n{}", out.stdout);
}

// ── Bad file: counterexamples ─────────────────────────────────────────────────

#[test]
fn bad_file_exits_nonzero() {
    let out = run_file("bad.cantor");
    assert_ne!(out.code, 0, "bad.cantor should exit non-zero\nstdout: {}", out.stdout);
}

#[test]
fn bad_file_reports_counterexamples() {
    let out = run_file("bad.cantor");
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved result line in output:\n{}", out.stdout
    );
}

#[test]
fn bad_file_summary_line() {
    let out = run_file("bad.cantor");
    assert!(
        out.stdout.contains("0 proved"),
        "expected '0 proved' in summary:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("2 counterexample"),
        "expected '2 counterexample' in summary:\n{}", out.stdout
    );
}

#[test]
fn counterexample_output_shows_witness_and_range() {
    // The output should tell the developer what values caused the violation
    // and which range was not satisfied.
    let out = run_file("bad.cantor");
    assert!(
        out.stdout.contains("->  output ="),
        "expected witness format 'x = N  ->  output = M':\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("not in"),
        "expected 'not in <Range>' in output:\n{}", out.stdout
    );
    // Specific range names should appear.
    assert!(out.stdout.contains("Int16"), "expected Int16 range:\n{}", out.stdout);
    assert!(out.stdout.contains("Nat"),   "expected Nat range:\n{}", out.stdout);
}

// ── cantor run ────────────────────────────────────────────────────────────────

#[test]
fn run_executes_main_and_prints_result() {
    // run_demo.cantor: abs(-21) = 21, double(21) = 42
    let out = run_subcommand("run_demo.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 42"),
        "expected 'main() = 42' in output:\n{}", out.stdout
    );
}

#[test]
fn run_also_shows_proof_results() {
    let out = run_subcommand("run_demo.cantor");
    assert!(out.stdout.contains("  proved  "), "expected proved lines:\n{}", out.stdout);
    assert!(out.stdout.contains("3 proved"),   "expected summary:\n{}", out.stdout);
}

#[test]
fn run_refuses_when_counterexample_found() {
    // bad_with_main.cantor: `broken : Nat -> Nat` has a counterexample.
    let out = run_subcommand("bad_with_main.cantor");
    assert_ne!(out.code, 0, "should refuse to run on counterexample");
    assert!(
        out.stderr.contains("not running"),
        "expected refusal message on stderr:\n{}", out.stderr
    );
}

#[test]
fn run_still_prints_check_results_before_refusing() {
    let out = run_subcommand("bad_with_main.cantor");
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line in stdout:\n{}", out.stdout
    );
}

#[test]
fn run_no_main_function_exits_nonzero() {
    // good.cantor has no `main` function.
    let out = run_subcommand("good.cantor");
    assert_ne!(out.code, 0, "should fail without main");
    assert!(
        out.stderr.contains("main"),
        "expected error about missing main:\n{}", out.stderr
    );
}

#[test]
fn run_usage_shown_for_missing_arg() {
    // `cantor run` with no file should show usage.
    let out = run(&["run"]);
    assert_eq!(out.code, 2);
    assert!(out.stderr.contains("usage"), "expected usage hint:\n{}", out.stderr);
}

// ── Constants ─────────────────────────────────────────────────────────────────

#[test]
fn const_demo_proves_and_runs() {
    // const_demo.cantor defines `base : Nat = 10` and `tau : Nat = 2 * 314`,
    // then uses them in a function; main() should return 638.
    let out = run_subcommand("const_demo.cantor");
    assert_eq!(out.code, 0, "expected exit 0:\n{}\n{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("638"),
        "expected main() = 638 in output:\n{}", out.stdout
    );
}

#[test]
fn const_demo_shows_proved_for_constants() {
    let out = run_subcommand("const_demo.cantor");
    assert!(
        out.stdout.contains("base : Nat = 10"),
        "expected constant display in output:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("4 proved"),
        "expected 4 proved in summary:\n{}", out.stdout
    );
}

// ── Bool domain and range ─────────────────────────────────────────────────────

#[test]
fn bool_demo_all_proved() {
    let out = run_file("bool_demo.cantor");
    assert_eq!(out.code, 0, "bool_demo.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample result line:\n{}", out.stdout
    );
}

#[test]
fn bool_demo_shows_bool_signatures() {
    let out = run_file("bool_demo.cantor");
    assert!(out.stdout.contains("Int -> Bool"), "expected 'Int -> Bool' sig:\n{}", out.stdout);
    assert!(out.stdout.contains("Bool -> Bool"), "expected 'Bool -> Bool' sig:\n{}", out.stdout);
    assert!(out.stdout.contains("Bool -> Nat"),  "expected 'Bool -> Nat' sig:\n{}", out.stdout);
}

#[test]
fn bool_run_executes_and_prints_result() {
    // negate(is_positive(-3)) = negate(false) = true, so main() = 99
    let out = run_subcommand("bool_run.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 99"),
        "expected 'main() = 99' in output:\n{}", out.stdout
    );
}

#[test]
fn bool_run_proves_all_sigs() {
    let out = run_subcommand("bool_run.cantor");
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
}

// ── assert / Fail / ? runtime behaviour ──────────────────────────────────────

#[test]
fn assert_pass_prints_value() {
    // assert_pass.cantor: safe_to_nat(42)? succeeds, main() = 43.
    let out = run_subcommand("assert_pass.cantor");
    assert_eq!(out.code, 0, "expected success:\n{}\n{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("43"),
        "expected main() = 43 in output:\n{}", out.stdout
    );
}

#[test]
fn assert_fail_exits_nonzero() {
    // assert_fail.cantor: safe_to_nat(-5)? fails at runtime.
    let out = run_subcommand("assert_fail.cantor");
    assert_ne!(out.code, 0, "expected failure:\n{}\n{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("assertion failed"),
        "expected assertion-failed message on stderr:\n{}", out.stderr
    );
}

#[test]
fn assert_pass_still_proves_sigs() {
    // The checker runs before codegen: both sigs should say `proved`.
    let out = run_subcommand("assert_pass.cantor");
    assert!(
        out.stdout.contains("proved"),
        "expected `proved` in checker output:\n{}", out.stdout
    );
}
