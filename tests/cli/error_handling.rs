use super::helpers::*;

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
fn sentinel_collision_rejected() {
    // `Fail` used to be encoded as a sentinel integer, so `Nat | (Fail * Int)`'s
    // membership check collapsed to Unconstrained (the unbounded `Int` payload's
    // decode predicate holds for nearly every representable value) — this
    // program used to falsely prove despite always returning `-1 ∉ Nat`.
    let out = run_file("sentinel_collision.cantor");
    assert_ne!(out.code, 0, "sentinel_collision.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  buggy"),
        "expected counterexample for buggy:\n{}", out.stdout
    );
}

#[test]
fn try_extraction_arithmetic_runs_end_to_end() {
    // `Fail` used to be a sentinel integer, so a `?`-unwrapped value already
    // happened to be plain-integer-sorted; now that `Fail` is a distinct
    // sort routed through the cross-kind union datatype machinery, `?` must
    // explicitly extract the success value before arithmetic (`y - 1`) can
    // be applied to it. This exercises that end-to-end, not just in the
    // solver: fetch(10) succeeds with 10, so main() should compute 10-1=9.
    let out = run_subcommand("try_extraction_arithmetic.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("2 proved"),
        "expected '2 proved' in summary:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("main() = 9"),
        "expected 'main() = 9' in output:\n{}", out.stdout
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
