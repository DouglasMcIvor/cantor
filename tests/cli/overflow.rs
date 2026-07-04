//! int-soundness-plan phase 1 — checked arithmetic, end to end.
//!
//! Counterexample/unknown overflow obligations must never be a compile-time
//! refusal (see soundness_diagnostics.rs's `assert_run_refused` for what a
//! *real* refusal looks like — these tests assert the opposite: the file
//! still reports fully `proved` and `cantor run` still executes).

use super::helpers::*;

#[test]
fn unbounded_mul_aborts_at_runtime_not_a_wrong_value() {
    let out = run_subcommand("overflow_mul.cantor");
    assert_ne!(
        out.code, 0,
        "overflow_mul.cantor should abort at runtime:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("arithmetic overflow"),
        "expected overflow abort message on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("not running"),
        "must not be refused at compile time — overflow is a runtime concern:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("proved          mul"),
        "the range claim itself (Int*Int -> Int) is still proved:\n{}",
        out.stdout
    );
}

#[test]
fn unbounded_mul_runs_normally_when_no_overflow_occurs() {
    let out = run_subcommand("overflow_mul_ok.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 42"),
        "expected correct result:\n{}",
        out.stdout
    );
}

#[test]
fn unbounded_add_aborts_at_i64_max() {
    let out = run_subcommand("overflow_add.cantor");
    assert_ne!(
        out.code, 0,
        "overflow_add.cantor should abort at runtime:\n{}",
        out.stdout
    );
    assert!(
        out.stderr.contains("arithmetic overflow"),
        "stderr: {}",
        out.stderr
    );
}

#[test]
fn unbounded_sub_aborts() {
    let out = run_subcommand("overflow_sub.cantor");
    assert_ne!(
        out.code, 0,
        "overflow_sub.cantor should abort at runtime:\n{}",
        out.stdout
    );
    assert!(
        out.stderr.contains("arithmetic overflow"),
        "stderr: {}",
        out.stderr
    );
}

#[test]
fn negating_i64_min_aborts() {
    let out = run_subcommand("overflow_neg.cantor");
    assert_ne!(
        out.code, 0,
        "overflow_neg.cantor should abort at runtime:\n{}",
        out.stdout
    );
    assert!(
        out.stderr.contains("arithmetic overflow"),
        "stderr: {}",
        out.stderr
    );
}

#[test]
fn division_of_i64_min_by_neg_one_aborts() {
    // The one case division can overflow: divisor-nonzero (a separate, hard
    // proof gate) is satisfied here, but MIN/-1 is UB in LLVM's sdiv.
    let out = run_subcommand("overflow_div_min_neg1.cantor");
    assert_ne!(
        out.code, 0,
        "overflow_div_min_neg1.cantor should abort at runtime:\n{}",
        out.stdout
    );
    assert!(
        out.stderr.contains("arithmetic overflow"),
        "stderr: {}",
        out.stderr
    );
}

#[test]
fn ordinary_division_unaffected_by_overflow_channel() {
    // Regression: the new MIN/-1 guard must not interfere with normal
    // division, nor with the existing divisor-nonzero obligation.
    let out = run_subcommand("overflow_div_ok.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3"),
        "expected correct result:\n{}",
        out.stdout
    );
}

#[test]
fn bounded_multiply_at_extreme_values_runs_correctly() {
    // Int32*Int32 -> Int: the solver should prove no i64 overflow is
    // possible, eliding the check — this asserts the elided path still
    // computes the right answer (the elision decision itself is asserted
    // directly against `ConstrainedTree::overflow_checks` in
    // tests/solver/overflow.rs; `llvm-ir` can't help here since that
    // subcommand deliberately skips the solver and would show a checked
    // instruction either way).
    let out = run_subcommand("overflow_bounded_mul.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 4611686014132420609"),
        "expected 2147483647*2147483647:\n{}",
        out.stdout
    );
}
