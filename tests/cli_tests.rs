//! Integration tests for the `cantor` CLI binary.
//!
//! These tests run the compiled binary as a subprocess and check its exit
//! codes, stdout, and stderr. They live alongside the `.cantor` fixture files
//! in `tests/cantor_files/` so that both evolve together as the CLI grows.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::{Command, Stdio};

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

#[derive(Debug)]
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

fn run_repl(input: &str) -> Output {
    let mut cmd = cantor();
    cmd.stdin(Stdio::piped())
       .stdout(Stdio::piped())
       .stderr(Stdio::piped());
    let mut child = cmd.spawn().expect("failed to spawn cantor binary");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(input.as_bytes())
        .expect("failed to write to stdin");
    drop(child.stdin.take());
    let out = child.wait_with_output().expect("failed to wait for cantor binary");
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

fn run_llvm_ir(name: &str) -> Output {
    let path = fixture(name);
    run(&["llvm-ir", path.to_str().unwrap()])
}

/// Assert that `cantor run` refused to execute (the `ConstrainedTree` proof
/// gate — not every signature was `Proved`), regardless of whether the
/// culprit is a `Counterexample` or an `Unknown`.
fn assert_run_refused(out: &Output) {
    assert_ne!(out.code, 0, "should refuse to run\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("not running"),
        "expected refusal message on stderr:\n{}", out.stderr
    );
}

/// Assert that `cantor run` refused to execute because at least one signature
/// was `Unknown` — the `ConstrainedTree` proof gate means this is no longer
/// the "warning: ... running anyway" case it used to be.
fn assert_run_refused_due_to_unknown(out: &Output) {
    assert_run_refused(out);
    assert!(
        out.stdout.contains("  unknown  "),
        "expected an `unknown` line in the check report:\n{}", out.stdout
    );
}

// ── No-arg / REPL ────────────────────────────────────────────────────────────

#[test]
fn no_args_starts_repl_and_exits_cleanly_on_eof() {
    let out = run_repl("");
    assert_eq!(out.code, 0, "REPL should exit 0 on EOF, got: {out:?}");
    assert!(
        out.stdout.contains("Goodbye"),
        "expected goodbye message, got stdout: {:?}", out.stdout
    );
}

#[test]
fn repl_quit_command_exits_cleanly() {
    let out = run_repl(":quit\n");
    assert_eq!(out.code, 0, "expected exit 0 after :quit");
}

#[test]
fn repl_help_command_shows_commands() {
    let out = run_repl(":help\n:quit\n");
    assert!(
        out.stdout.contains(":quit"),
        "expected :help to list :quit, got: {:?}", out.stdout
    );
}

#[test]
fn repl_set_alias_reports_defined() {
    // Unannotated set aliases have nothing to verify; the REPL reports "defined".
    let out = run_repl("Colour = {1, 2, 3}\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("defined"),
        "expected 'defined' for set alias, got: {:?}", out.stdout
    );
}

#[test]
fn repl_annotated_definition_shows_proved() {
    // A function with a signature gets verified immediately.
    // The sig and implementation are entered over two lines (multi-line input).
    let out = run_repl("double : Int -> Int\ndouble(x) = x * 2\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("proved"),
        "expected 'proved' for annotated function, got: {:?}", out.stdout
    );
}

#[test]
fn repl_expression_evaluation_returns_result() {
    let out = run_repl("1 + 1\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains('2'),
        "expected result 2, got: {:?}", out.stdout
    );
}

#[test]
fn repl_defs_command_lists_definitions() {
    let out = run_repl("double : Int -> Int\ndouble(x) = x * 2\n:defs\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("double"),
        "expected :defs to list 'double', got: {:?}", out.stdout
    );
}

#[test]
fn repl_reset_clears_definitions() {
    let out = run_repl("double : Int -> Int\ndouble(x) = x * 2\n:reset\n:defs\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("no definitions"),
        "expected no definitions after :reset, got: {:?}", out.stdout
    );
}

#[test]
fn repl_bad_args_prints_usage() {
    let out = run(&["run"]);
    assert_eq!(out.code, 2, "expected exit 2 for bad args");
    assert!(out.stderr.contains("usage"), "expected usage on stderr");
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

// ── cantor llvm-ir ───────────────────────────────────────────────────────────

#[test]
fn llvm_ir_exits_zero_and_prints_module() {
    let out = run_llvm_ir("good.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(out.stdout.contains("define"), "expected LLVM IR function definitions:\n{}", out.stdout);
}

#[test]
fn llvm_ir_skips_the_solver() {
    // No proof-checking output (`proved`/`counterexample`/`unknown` lines) —
    // llvm-ir is a pure codegen debugging tool, it never invokes the SMT solver.
    let out = run_llvm_ir("good.cantor");
    assert!(
        !out.stdout.contains("proved") && !out.stdout.contains("counterexample"),
        "expected no solver output:\n{}", out.stdout
    );
}

#[test]
fn llvm_ir_runs_even_with_a_counterexample() {
    // bad.cantor has a function the solver disproves; llvm-ir doesn't care —
    // it never runs the solver, so it should still emit valid IR.
    let out = run_llvm_ir("bad.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(out.stdout.contains("define"), "expected LLVM IR function definitions:\n{}", out.stdout);
}

#[test]
fn llvm_ir_shows_tagged_union_wire_type_for_disjoint_union() {
    // Regression test for the kind.rs Add fix: `{0} + NatPos` must compile to
    // a `{ i32, i64 }` TaggedUnion struct, never a bare i64 or a 2-element Tuple.
    let out = run_llvm_ir("set_ops_run.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("@accept_nat({ i32, i64 }"),
        "expected accept_nat's TaggedUnion param wire type:\n{}", out.stdout
    );
}

#[test]
fn llvm_ir_reports_compile_error_for_unsound_bool_int_narrowing() {
    // Regression test: `Bool | Nat -> Bool; bad(x) = x` requires narrowing a
    // mixed-Kind TaggedUnion down to Bool, which used to silently truncate the
    // raw i64 payload (ignoring the tag) instead of failing. Bool and Int are
    // disjoint in Cantor's value model, so this must be a clean compile error
    // even under `llvm-ir`, which otherwise skips the solver entirely.
    let out = run_llvm_ir("bool_nat_narrow_bad.cantor");
    assert_eq!(out.code, 1, "expected exit 1\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("compile error"),
        "expected a compile error on stderr:\n{}", out.stderr
    );
}

#[test]
fn llvm_ir_usage_shown_for_missing_arg() {
    let out = run(&["llvm-ir"]);
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

// ── !! (error-union) solver checks ───────────────────────────────────────────

#[test]
fn error_union_proof_exits_zero() {
    let out = run_file("error_union_proof.cantor");
    assert_eq!(out.code, 0, "error_union_proof.cantor should exit 0\nstdout: {}", out.stdout);
}

#[test]
fn error_union_proof_shows_proved() {
    let out = run_file("error_union_proof.cantor");
    assert!(
        out.stdout.contains("  proved  "),
        "expected '  proved  ' result line:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample in output:\n{}", out.stdout
    );
}

#[test]
fn error_union_proof_signature_shows_desugared_range() {
    // `!!` desugars to `| (Fail * ...)` at parse time, so the displayed signature
    // shows the canonical form rather than the original `!!` notation.
    let out = run_file("error_union_proof.cantor");
    assert!(
        out.stdout.contains("Nat | Fail * HTTPError"),
        "expected 'Nat | Fail * HTTPError' in signature output:\n{}", out.stdout
    );
}

#[test]
fn error_union_bad_exits_nonzero() {
    // bad_fetch returns x which can be negative — not in Nat !! HTTPError.
    let out = run_file("error_union_bad.cantor");
    assert_ne!(out.code, 0, "error_union_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
}

#[test]
fn error_union_bad_shows_counterexample() {
    let out = run_file("error_union_bad.cantor");
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved result line:\n{}", out.stdout
    );
}

// ── !! (error-union) run tests ────────────────────────────────────────────────

#[test]
fn error_union_run_proves_all_sigs() {
    let out = run_subcommand("error_union_run.cantor");
    assert!(
        out.stdout.contains("2 proved"),
        "expected '2 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn error_union_run_success_path_returns_value() {
    // fetch(10) succeeds; main() should return 10.
    let out = run_subcommand("error_union_run.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 10"),
        "expected 'main() = 10' in output:\n{}", out.stdout
    );
}

#[test]
fn error_union_propagate_proves_all_sigs() {
    let out = run_subcommand("error_union_propagate.cantor");
    assert!(
        out.stdout.contains("2 proved"),
        "expected '2 proved' in summary:\n{}", out.stdout
    );
}

#[test]
fn error_union_propagate_exits_with_error_code() {
    // fetch(-1) fails with `fail 503`; `?` propagates it; main exits 1 reporting 503.
    let out = run_subcommand("error_union_propagate.cantor");
    assert_eq!(out.code, 1, "expected exit 1 (failure)\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("503"),
        "expected error code 503 in stderr:\n{}", out.stderr
    );
}

// ── Runtime sets ──────────────────────────────────────────────────────────────

#[test]
fn runtime_set_runs_and_returns_correct_result() {
    // runtime_set.cantor:
    //   sum({2,3,5,7}) = 17
    //   membership checks: 3 in primes (✓) + 4 not in primes (✓) = 2
    //   size({2,3,5,7}) = 4
    //   total = 17 + 2 + 4 = 23
    let out = run_subcommand("runtime_set.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 23"),
        "expected 'main() = 23' in output:\n{}", out.stdout
    );
}

#[test]
fn runtime_set_proves_signature() {
    // `main : -> Int` with a Set(Int) body is now fully proved — the solver
    // models runtime sets as opaque integers and treats membership/size as
    // unconstrained, which is sufficient for an Int return range.
    let out = run_subcommand("runtime_set.cantor");
    assert!(
        out.stdout.contains("  proved  "),
        "expected proved result in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  unknown  "),
        "unexpected unknown in output:\n{}", out.stdout
    );
}

// ── Tuples / anonymous product types ──────────────────────────────────────────

#[test]
fn tuple_basics_all_proved() {
    let out = run_file("tuple_basics.cantor");
    assert_eq!(out.code, 0, "tuple_basics.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("5 proved"),
        "expected '5 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn tuple_basics_shows_product_signatures() {
    let out = run_file("tuple_basics.cantor");
    assert!(out.stdout.contains("Int * Int -> Int"), "fst/snd sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("Nat * Nat -> Nat"), "sum_pair sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("Int * Int -> Int * Int"), "swap/identity sig missing:\n{}", out.stdout);
}

#[test]
fn tuple_run_prints_tuple_result() {
    // swap((3, 9)) = (9, 3)
    let out = run_subcommand("tuple_run.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = (9, 3)"),
        "expected 'main() = (9, 3)' in output:\n{}", out.stdout
    );
}

#[test]
fn tuple_run_proves_all_sigs() {
    let out = run_subcommand("tuple_run.cantor");
    assert!(
        out.stdout.contains("2 proved"),
        "expected '2 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn tuple_bad_counterexample() {
    // overflow_pair : Int16 * Int16 -> Int16 overflows when both elements are large.
    let out = run_file("tuple_bad.cantor");
    assert_ne!(out.code, 0, "tuple_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved line:\n{}", out.stdout
    );
}

#[test]
fn tuple_bad_counterexample_mentions_range() {
    let out = run_file("tuple_bad.cantor");
    assert!(
        out.stdout.contains("not in Int16"),
        "expected 'not in Int16' in counterexample output:\n{}", out.stdout
    );
}

// ── Destructuring ─────────────────────────────────────────────────────────────

#[test]
fn destructure_basics_all_proved() {
    let out = run_file("destructure_basics.cantor");
    assert_eq!(out.code, 0, "destructure_basics.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected no failures:\n{}", out.stdout
    );
}

#[test]
fn destructure_basics_run_produces_correct_output() {
    let out = run_subcommand("destructure_basics.cantor");
    assert_eq!(out.code, 0, "destructure_basics.cantor run should exit 0\nstdout: {}", out.stdout);
    // main() returns -3 + 4 = 1
    assert!(
        out.stdout.contains("1"),
        "expected output 1 from destructure_basics.cantor main:\n{}", out.stdout
    );
}

#[test]
fn destructure_bad_gives_counterexample() {
    let out = run_file("destructure_bad.cantor");
    assert_ne!(out.code, 0, "destructure_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
}

#[test]
fn destructure_mut_run_produces_correct_output() {
    let out = run_subcommand("destructure_mut.cantor");
    assert_eq!(out.code, 0, "destructure_mut.cantor run should exit 0\nstdout: {}", out.stdout);
    // main() computes (-3 + 4) + (4 + -3) = 1 after swap; a+b = 4 + (-3) = 1
    assert!(
        out.stdout.contains("1"),
        "expected output 1 from destructure_mut.cantor main:\n{}", out.stdout
    );
}

#[test]
fn destructure_partial_all_proved() {
    let out = run_file("destructure_partial.cantor");
    assert_eq!(out.code, 0, "destructure_partial.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected no failures:\n{}", out.stdout
    );
}

#[test]
fn destructure_partial_run_produces_correct_output() {
    let out = run_subcommand("destructure_partial.cantor");
    assert_eq!(out.code, 0, "destructure_partial.cantor run should exit 0\nstdout: {}", out.stdout);
    // main() returns 1 + 2 + 3 = 6
    assert!(
        out.stdout.contains("6"),
        "expected output 6 from destructure_partial.cantor main:\n{}", out.stdout
    );
}

// ── Set operations (`+` disjoint union, `^` symmetric difference) ────────────

#[test]
fn set_ops_proof_all_proved() {
    let out = run_file("set_ops_proof.cantor");
    assert_eq!(out.code, 0, "set_ops_proof.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn set_ops_proof_shows_set_op_signatures() {
    let out = run_file("set_ops_proof.cantor");
    assert!(out.stdout.contains("Nat ^ {0} -> NatPos"), "strip_zero sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("{0} + NatPos -> Nat"), "accept_nat sig missing:\n{}", out.stdout);
}

#[test]
fn set_ops_bad_overlapping_union_gives_counterexample() {
    // {0, 1} + {1, 2} is invalid because 1 is in both sets.
    let out = run_file("set_ops_bad.cantor");
    assert_ne!(out.code, 0, "set_ops_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved line:\n{}", out.stdout
    );
}

#[test]
fn set_ops_bad_counterexample_mentions_not_disjoint() {
    let out = run_file("set_ops_bad.cantor");
    assert!(
        out.stdout.contains("not disjoint"),
        "expected 'not disjoint' in counterexample message:\n{}", out.stdout
    );
}

#[test]
fn set_ops_run_produces_correct_output() {
    // set_ops_run.cantor: accept_nat(7) + strip_zero(3) = 7 + 3 = 10.
    // Regression test for the TaggedUnion narrow/widen codegen paths that
    // back `+` (forced-disjoint union) at runtime — both at function return
    // and at the call-argument boundary (accept_nat(7) widens the literal
    // into a {0} + NatPos tagged value; `main(x) = x` narrows it back).
    let out = run_subcommand("set_ops_run.cantor");
    assert_eq!(out.code, 0, "set_ops_run.cantor run should exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 10"),
        "expected 'main() = 10' in output:\n{}", out.stdout
    );
}

// ── Kleene-star vectors (X* via sequence theory) ─────────────────────────────

#[test]
fn vectors_kleene_demo_all_proved() {
    let out = run_file("vectors_kleene_demo.cantor");
    assert_eq!(out.code, 0, "vectors_kleene_demo.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}", out.stdout
    );
}

// ── Kleene-star vectors: Arrow runtime (Int* and Bool*) ──────────────────────

#[test]
fn vectors_runtime_all_proved() {
    let out = run_file("vectors_runtime.cantor");
    assert_eq!(out.code, 0, "vectors_runtime.cantor check should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}", out.stdout
    );
}

#[test]
fn vectors_runtime_run_returns_len_of_composed_vector() {
    // main() = get_len(identity_int(make_int_vec())) = len([1,2,3]) = 3
    let out = run_subcommand("vectors_runtime.cantor");
    assert_eq!(out.code, 0, "vectors_runtime.cantor run should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("3"),
        "expected output 3 (len of [1,2,3]):\n{}", out.stdout
    );
}

// ── Nested vectors (X**) ─────────────────────────────────────────────────────

#[test]
fn vectors_nested_pure_fns_proved() {
    // Pure-expression-body functions on Nat** must be fully proved by the solver.
    // (inner_len/get_elem, this fixture's block-body functions, are NOT checked
    // here — they index a fixed position into an unconstrained Nat**/Nat*
    // parameter with no minimum-length guarantee, which the solver now
    // correctly reports as a Counterexample now that `return` is checked at
    // all, rather than masking it behind a blanket Unknown. That's a genuine,
    // known gap in these fixtures' signatures, deliberately left as-is.)
    let out = run_file("vectors_nested.cantor");
    assert!(out.stdout.contains("proved          make_nested"), "make_nested not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          identity_nested"), "identity_nested not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          outer_len"),   "outer_len not proved:\n{}",  out.stdout);
}

#[test]
fn vectors_nested_run_outer_len() {
    // vectors_nested.cantor also defines concat_nested, which is Unknown
    // (early-return solver limitation, unrelated to outer_len) — the
    // ConstrainedTree gate is whole-file, so `cantor run` refuses even
    // though `main` itself never calls concat_nested.
    let out = run_subcommand("vectors_nested.cantor");
    assert_run_refused_due_to_unknown(&out);
}

#[test]
fn vectors_nested_deep_index_and_concat() {
    // concat_len (early-return) is Unknown; the whole-file ConstrainedTree
    // gate means `cantor run` now refuses regardless of get_deep's own proof.
    let out = run_subcommand("vectors_nested_index.cantor");
    assert_run_refused_due_to_unknown(&out);
}

// ── Triple-nested vectors (Nat***) ───────────────────────────────────────────

#[test]
fn vectors_triple_nested_run_deep_index() {
    // Same early-return Unknown pattern as the other vectors_* fixtures.
    let out = run_subcommand("vectors_triple_nested.cantor");
    assert_run_refused_due_to_unknown(&out);
}

// ── Struct vectors ((A * B)*) ────────────────────────────────────────────────

#[test]
fn vectors_struct_pure_fns_proved() {
    // make_pairs, pair_vec_len, first_fst, third_snd, and main are provable:
    // literal-array indexing has tuple sort in the solver (no bounds obligation),
    // so ApplySelector resolves field access statically.
    let out = run_file("vectors_struct.cantor");
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
    assert!(out.stdout.contains("proved          make_pairs"),   "make_pairs not proved:\n{}",   out.stdout);
    assert!(out.stdout.contains("proved          pair_vec_len"), "pair_vec_len not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          first_fst"),    "first_fst not proved:\n{}",    out.stdout);
    assert!(out.stdout.contains("proved          third_snd"),    "third_snd not proved:\n{}",    out.stdout);
}

#[test]
fn vectors_struct_run_outer_len() {
    // vectors_struct.cantor also defines concat_struct, which is Unknown
    // (early-return solver limitation) — whole-file gate refuses the run.
    let out = run_subcommand("vectors_struct.cantor");
    assert_run_refused_due_to_unknown(&out);
}

#[test]
fn vectors_struct_literal_index_proj() {
    // first_fst() = [(1,10),(2,20),(3,30)][0].0 = 1
    // All three functions are proved (literal arrays have tuple sort → statically provable).
    let out = run_subcommand("vectors_struct_fst.cantor");
    assert_eq!(out.code, 0, "run should exit 0\nstdout: {}", out.stdout);
    assert!(out.stdout.contains("main() = 1"), "expected 'main() = 1':\n{}", out.stdout);
    assert!(out.stdout.contains("proved          first_fst"), "first_fst not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          third_snd"), "third_snd not proved:\n{}", out.stdout);
}

#[test]
fn vectors_struct_block_index_and_concat() {
    // Same fixture/reason as vectors_struct_run_outer_len — no counterexamples,
    // but concat_struct's Unknown result still refuses the whole-file run.
    let out = run_subcommand("vectors_struct.cantor");
    assert_run_refused_due_to_unknown(&out);
    assert!(!out.stdout.contains("  counterexample  "), "unexpected counterexample:\n{}", out.stdout);
}

// ── Vectors: block-body coercion, xs[i] indexing, ++ concatenation ───────────

#[test]
fn vectors_extended_no_counterexamples() {
    // Block-body functions using `return` on `let`-bound vector locals
    // (block_coerce_len, concat_lit, bool_concat_len) are correctly Unknown —
    // the solver can't yet reason about len()/++ on an opaque runtime vector
    // binding, a separate, known gap from `return` itself.
    //
    // get_second is a genuine, expected exception: it indexes a fixed
    // position into an unconstrained `Nat*` parameter with no minimum-length
    // guarantee, which the solver now correctly reports as a Counterexample
    // now that `return` is checked at all (previously masked behind the
    // blanket "early return unsupported" Unknown). This is deliberately left
    // as-is rather than tightening the fixture's signature.
    let out = run_file("vectors_extended.cantor");
    assert!(
        out.stdout.contains("counterexample  get_second"),
        "expected get_second's known counterexample:\n{}", out.stdout
    );
    let unexpected_counterexample = out.stdout.lines()
        .any(|l| l.contains("  counterexample  ") && !l.contains("get_second"));
    assert!(!unexpected_counterexample, "unexpected counterexample:\n{}", out.stdout);
}

#[test]
fn vectors_extended_concat_coerce_block_len() {
    // concat_lit uses an early `return` — Unknown (solver limitation), so
    // the whole-file ConstrainedTree gate refuses `cantor run`, even though
    // main() itself (which calls concat_lit) would compute the right answer.
    let out = run_subcommand("vectors_extended_concat.cantor");
    assert_run_refused_due_to_unknown(&out);
}

#[test]
fn vectors_extended_index_elem() {
    // get_elem indexes a fixed position into an unconstrained `Nat*`
    // parameter with no minimum-length guarantee — a genuine, known
    // Counterexample now that `return` is checked at all (previously masked
    // behind a blanket Unknown), not a Class of bug this fix addresses.
    // `cantor run` correctly refuses even though main()/make_vec are proved.
    let out = run_subcommand("vectors_extended_index.cantor");
    assert_run_refused(&out);
    assert!(
        out.stdout.contains("counterexample  get_elem"),
        "expected get_elem's known counterexample:\n{}", out.stdout
    );
}

#[test]
fn vectors_extended_bool_concat_len() {
    // bool_concat_len uses an early `return` — Unknown (solver limitation),
    // so `cantor run` refuses even though main() would compute the right answer.
    let out = run_subcommand("vectors_extended_bool_concat.cantor");
    assert_run_refused_due_to_unknown(&out);
}

// ── Vectors: repeated products and array literals ─────────────────────────────

#[test]
fn vectors_demo_all_proved() {
    let out = run_file("vectors_demo.cantor");
    assert_eq!(out.code, 0, "vectors_demo.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}", out.stdout
    );
}

#[test]
fn vectors_demo_run_produces_correct_output() {
    let out = run_subcommand("vectors_demo.cantor");
    assert_eq!(out.code, 0, "vectors_demo.cantor run should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("6"),
        "expected output 6 from sum3(1,2,3):\n{}", out.stdout
    );
}

// ── Bracket-depth newlines ────────────────────────────────────────────────────

#[test]
fn newline_paren_all_proved() {
    // Regression: bare ident at end of assignment followed by ( on the next line
    // must not be parsed as a function call (old bug: `b := tmp\n(a,b)` → `b := tmp(a,b)`).
    let out = run_file("newline_paren.cantor");
    assert_eq!(out.code, 0, "newline_paren.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected no failures:\n{}", out.stdout
    );
}

#[test]
fn newline_paren_run_produces_correct_output() {
    let out = run_subcommand("newline_paren.cantor");
    assert_eq!(out.code, 0, "newline_paren.cantor run should exit 0\nstdout: {}", out.stdout);
    // swap_test((-3, 7)) = (7, -3); main returns x + y = 7 + (-3) = 4
    assert!(
        out.stdout.contains("4"),
        "expected output 4 from newline_paren.cantor main:\n{}", out.stdout
    );
}

// ── --timeout flag ────────────────────────────────────────────────────────────

#[test]
fn timeout_flag_space_form_is_accepted() {
    let out = run(&["--timeout", "30", fixture("good.cantor").to_str().unwrap()]);
    assert_eq!(out.code, 0, "--timeout 30 should succeed\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(out.stdout.contains("proved"), "expected proved output:\n{}", out.stdout);
}

#[test]
fn timeout_flag_equals_form_is_accepted() {
    let out = run(&["--timeout=10", fixture("good.cantor").to_str().unwrap()]);
    assert_eq!(out.code, 0, "--timeout=10 should succeed\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(out.stdout.contains("proved"), "expected proved output:\n{}", out.stdout);
}

#[test]
fn timeout_flag_zero_disables_limit() {
    let out = run(&["--timeout=0", fixture("good.cantor").to_str().unwrap()]);
    assert_eq!(out.code, 0, "--timeout=0 should succeed\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(out.stdout.contains("proved"), "expected proved output:\n{}", out.stdout);
}

#[test]
fn timeout_flag_missing_value_errors() {
    let out = run(&["--timeout"]);
    assert_ne!(out.code, 0, "missing --timeout value should fail");
    assert!(out.stderr.contains("--timeout requires a value"), "expected error message:\n{}", out.stderr);
}

// ── Set difference in vector domains ─────────────────────────────────────────

// Previously panicked: `Nat* - A` was misparsed as `Nat * (-A)` (unary negation),
// causing an unreachable! in set_sort.  Now parsed correctly as KleeneStar(Nat) Sub A.

#[test]
fn vec_domain_set_diff_empty_set_counterexample() {
    // `(Nat* - {})` is just `Nat*` (empty set subtracted is a no-op).
    // `first_elem(xs) = xs[0]` gets a counterexample because xs could be empty.
    let out = run_file("vec_set_diff_domain.cantor");
    assert!(!out.stderr.contains("panicked"), "should not panic:\n{}", out.stderr);
    assert!(out.stdout.contains("counterexample"), "expected counterexample for first_elem:\n{}", out.stdout);
}

#[test]
fn vec_domain_set_diff_named_set_counterexample() {
    // `(Nat* - Nat)` — sequences are disjoint from integers; effectively `Nat*`.
    // Also gets a counterexample (empty vector).
    let out = run_file("vec_set_diff_domain.cantor");
    assert!(!out.stderr.contains("panicked"), "should not panic:\n{}", out.stderr);
    let lines: Vec<&str> = out.stdout.lines().collect();
    let ce_lines: Vec<&&str> = lines.iter().filter(|l| l.contains("counterexample")).collect();
    assert!(ce_lines.len() >= 2, "expected counterexample for both first_elem and first_elem2:\n{}", out.stdout);
}

#[test]
fn vec_domain_set_diff_pass_through_proved() {
    // `pass_through : (Nat* - {}) -> Nat*` — identity on the same domain/range is proved.
    let out = run_file("vec_set_diff_domain.cantor");
    assert!(out.stdout.contains("proved"), "expected pass_through to be proved:\n{}", out.stdout);
}

#[test]
fn timeout_flag_non_integer_errors() {
    let out = run(&["--timeout", "abc", fixture("good.cantor").to_str().unwrap()]);
    assert_ne!(out.code, 0, "non-integer --timeout should fail");
    assert!(out.stderr.contains("non-negative integer"), "expected error message:\n{}", out.stderr);
}

// ── Sequence unification: scalar/tuple ↔ vector boxing ───────────────────────

#[test]
fn vec_scalar_return_proved() {
    // `foo : -> Nat*; foo() = 5` — scalar 5 is the length-1 sequence [5]; proved.
    let out = run_file("vec_scalar_box.cantor");
    assert!(out.stdout.contains("proved          foo"), "expected foo proved:\n{}", out.stdout);
}

#[test]
fn vec_scalar_call_arg_proved() {
    // `val() = get(5)` where get expects Nat* — proved because 5 ∈ Nat* - {[]}.
    let out = run_file("vec_scalar_box.cantor");
    assert!(out.stdout.contains("proved          val"), "expected val proved:\n{}", out.stdout);
}

#[test]
fn vec_scalar_box_runs_len_1() {
    // JIT: `main() = len(foo())` where `foo() = 5 : Nat*` — length is 1.
    let out = run_subcommand("vec_scalar_box.cantor");
    assert_eq!(out.code, 0, "should exit 0:\n{}", out.stderr);
    assert!(out.stdout.contains("main() = 1"), "expected len 1:\n{}", out.stdout);
}

#[test]
fn vec_tuple_box_return_proved() {
    // `pair : -> Nat*; pair() = (3, 4)` — tuple (3,4) is the length-2 sequence [3,4]; proved.
    let out = run_file("vec_tuple_box.cantor");
    assert!(out.stdout.contains("proved          pair"), "expected pair proved:\n{}", out.stdout);
}

#[test]
fn vec_tuple_box_runs_len_2() {
    // JIT: `main() = len(pair())` where `pair() = (3, 4) : Nat*` — length is 2.
    let out = run_subcommand("vec_tuple_box.cantor");
    assert_eq!(out.code, 0, "should exit 0:\n{}", out.stderr);
    assert!(out.stdout.contains("main() = 2"), "expected len 2:\n{}", out.stdout);
}

#[test]
fn vec_length_narrowing_h_proved() {
    // `h : (Nat* - Nat - {[]}) -> Nat` — domain length ≥ 2 discharges xs[0] and xs[1].
    let out = run_file("vec_length_narrowing.cantor");
    assert!(out.stdout.contains("proved          h :"), "expected h proved:\n{}", out.stdout);
}

#[test]
fn vec_length_narrowing_control_counterexample() {
    // `h_no_empty_guard : (Nat* - Nat) -> Nat` — length ≠ 1 but empty still allowed → counterexample.
    let out = run_file("vec_length_narrowing.cantor");
    assert!(
        out.stdout.contains("counterexample  h_no_empty_guard"),
        "expected h_no_empty_guard counterexample:\n{}", out.stdout
    );
}

// ── Call-site domain obligations (end-to-end) ─────────────────────────────────

#[test]
fn call_domain_violation_counterexample() {
    // `bad(x) = safe_div(x, 0)` violates safe_div's `Int - {0}` domain: the
    // call site must fail to prove, or a proved program divides by zero.
    let out = run_file("call_domain_violation.cantor");
    assert_ne!(out.code, 0, "call_domain_violation.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  bad"),
        "expected counterexample for bad:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected call-site domain reason:\n{}", out.stdout
    );
}

#[test]
fn call_domain_violation_callee_still_proved() {
    // safe_div itself is fine — only the caller is at fault.
    let out = run_file("call_domain_violation.cantor");
    assert!(
        out.stdout.contains("proved          safe_div"),
        "expected safe_div proved:\n{}", out.stdout
    );
}

#[test]
fn loop_body_obligation_counterexample() {
    // Division by zero inside a while body, feeding a variable whose `Int`
    // invariant imposes no constraint — previously proved, then SIGFPE'd
    // under `cantor run`.
    let out = run_file("loop_body_obligation.cantor");
    assert_ne!(out.code, 0, "loop_body_obligation.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  h"),
        "expected counterexample for h:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("division by zero"),
        "expected division-by-zero reason:\n{}", out.stdout
    );
}

// ── Non-integer block locals (end-to-end) ──────────────────────────────────────

#[test]
fn bool_tuple_lets_prove_and_run() {
    // Bool and tuple `let`s in block bodies used to abort the cvc5 process
    // (integer-sorted SSA constants); now they prove and execute.
    let out = run_subcommand("bool_tuple_lets.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("main() = 42"),
        "expected 'main() = 42' in output:\n{}", out.stdout
    );
}

// ── Cross-kind comparison diagnostics (end-to-end) ─────────────────────────────

#[test]
fn kind_mismatch_eq_clean_error() {
    // `x == true` with x : Int used to reach cvc5 as an ill-sorted term and
    // abort with a raw C++ error; now it's a Cantor diagnostic.
    let out = run_file("kind_mismatch_eq.cantor");
    assert_ne!(out.code, 0, "kind_mismatch_eq.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stderr.contains("same value family"),
        "expected operand-family diagnostic on stderr:\n{}", out.stderr
    );
    assert!(
        !out.stderr.contains("cvc5"),
        "must not leak a raw cvc5 abort:\n{}", out.stderr
    );
}
