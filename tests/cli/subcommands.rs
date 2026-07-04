use super::helpers::*;

// ── cantor run ────────────────────────────────────────────────────────────────

#[test]
fn run_executes_main_and_prints_result() {
    // run_demo.cantor: abs(-21) = 21, double(21) = 42
    let out = run_subcommand("run_demo.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 42"),
        "expected 'main() = 42' in output:\n{}",
        out.stdout
    );
}

#[test]
fn run_also_shows_proof_results() {
    let out = run_subcommand("run_demo.cantor");
    assert!(
        out.stdout.contains("  proved  "),
        "expected proved lines:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("3 proved"),
        "expected summary:\n{}",
        out.stdout
    );
}

#[test]
fn run_refuses_when_counterexample_found() {
    // bad_with_main.cantor: `broken : Nat -> Nat` has a counterexample.
    let out = run_subcommand("bad_with_main.cantor");
    assert_ne!(out.code, 0, "should refuse to run on counterexample");
    assert!(
        out.stderr.contains("not running"),
        "expected refusal message on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn run_still_prints_check_results_before_refusing() {
    let out = run_subcommand("bad_with_main.cantor");
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line in stdout:\n{}",
        out.stdout
    );
}

#[test]
fn run_no_main_function_exits_nonzero() {
    // good.cantor has no `main` function.
    let out = run_subcommand("good.cantor");
    assert_ne!(out.code, 0, "should fail without main");
    assert!(
        out.stderr.contains("main"),
        "expected error about missing main:\n{}",
        out.stderr
    );
}

#[test]
fn run_usage_shown_for_missing_arg() {
    // `cantor run` with no file should show usage.
    let out = run(&["run"]);
    assert_eq!(out.code, 2);
    assert!(
        out.stderr.contains("usage"),
        "expected usage hint:\n{}",
        out.stderr
    );
}

// ── cantor llvm-ir ───────────────────────────────────────────────────────────

#[test]
fn llvm_ir_exits_zero_and_prints_module() {
    let out = run_llvm_ir("good.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("define"),
        "expected LLVM IR function definitions:\n{}",
        out.stdout
    );
}

#[test]
fn llvm_ir_skips_the_solver() {
    // No proof-checking output (`proved`/`counterexample`/`unknown` lines) —
    // llvm-ir is a pure codegen debugging tool, it never invokes the SMT solver.
    let out = run_llvm_ir("good.cantor");
    assert!(
        !out.stdout.contains("proved") && !out.stdout.contains("counterexample"),
        "expected no solver output:\n{}",
        out.stdout
    );
}

#[test]
fn llvm_ir_runs_even_with_a_counterexample() {
    // bad.cantor has a function the solver disproves; llvm-ir doesn't care —
    // it never runs the solver, so it should still emit valid IR.
    let out = run_llvm_ir("bad.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("define"),
        "expected LLVM IR function definitions:\n{}",
        out.stdout
    );
}

#[test]
fn llvm_ir_shows_tagged_union_wire_type_for_disjoint_union() {
    // Regression test for the kind.rs Add fix: `{0} + NatPos` must compile to
    // a `{ i32, i64 }` TaggedUnion struct, never a bare i64 or a 2-element Tuple.
    let out = run_llvm_ir("set_ops_run.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("@accept_nat({ i32, i64 }"),
        "expected accept_nat's TaggedUnion param wire type:\n{}",
        out.stdout
    );
}

#[test]
fn llvm_ir_reports_compile_error_for_unsound_bool_int_narrowing() {
    // Regression test: `Bool | Nat -> Bool; bad(x) = x` requires narrowing a
    // mixed-Kind TaggedUnion down to Bool, which used to silently truncate the
    // raw i64 payload (ignoring the tag) instead of failing. Bool and Int are
    // disjoint in Cantor's value model, so this must be a clean compile error
    // even under `llvm-ir`, which otherwise skips the solver entirely.
    //
    // This currently surfaces as an `Ice` (codegen's `narrow_tagged_union`
    // defense-in-depth check) rather than a `Diagnostic`, since elaboration
    // is expected to reject this before codegen ever sees it — see
    // CompileError's taxonomy in src/error.rs.
    let out = run_llvm_ir("bool_nat_narrow_bad.cantor");
    assert_eq!(
        out.code, 1,
        "expected exit 1\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("internal compiler error"),
        "expected an internal compiler error on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn llvm_ir_usage_shown_for_missing_arg() {
    let out = run(&["llvm-ir"]);
    assert_eq!(out.code, 2);
    assert!(
        out.stderr.contains("usage"),
        "expected usage hint:\n{}",
        out.stderr
    );
}
