use super::helpers::*;

// ── `none`/`None`, full coexistence with `Fail` ─────────────────────────────

#[test]
fn none_propagate_success_prints_value() {
    let out = run_subcommand("none_propagate_success.cantor");
    assert_eq!(
        out.code, 0,
        "expected success:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected 'main() = 5' in output:\n{}",
        out.stdout
    );
}

#[test]
fn none_propagate_none_exits_nonzero_with_message() {
    let out = run_subcommand("none_propagate_none.cantor");
    assert_ne!(
        out.code, 0,
        "expected non-zero exit:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("returned none"),
        "expected 'returned none' on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn none_propagate_fail_exits_nonzero_with_assertion_message() {
    let out = run_subcommand("none_propagate_fail.cantor");
    assert_ne!(
        out.code, 0,
        "expected non-zero exit:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("assertion failed"),
        "expected assertion-failed message on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn none_propagate_all_sigs_proved() {
    // All three fixtures share the same signatures; any one confirms the
    // checker accepts `Fail`/`None` coexisting in one range.
    let out = run_subcommand("none_propagate_success.cantor");
    assert!(
        out.stdout.contains("2 proved"),
        "expected '2 proved' in summary:\n{}",
        out.stdout
    );
}

#[test]
fn none_missing_from_range_rejected() {
    // `caller`'s own range is plain `Nat` — it never declares `None` — so a
    // `?` on a callee that can return `none` must be rejected at check time
    // rather than crashing codegen with an LLVM return-type mismatch.
    let out = run_file("none_missing_from_range.cantor");
    assert_ne!(
        out.code, 0,
        "none_missing_from_range.cantor should exit non-zero:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  caller"),
        "expected counterexample for caller:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("`None`"),
        "expected the missing-`None` diagnostic in output:\n{}",
        out.stdout
    );
}
