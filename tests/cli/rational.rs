//! The `Rational` numeric tower, end to end (docs/rational-plan.md).
//!
//! `/` is exact division, so `3 / 2` is a `Rational` rather than a truncated
//! `1`. The solver-level coverage lives in `tests/solver/rational.rs`; these
//! are the CLI tests that the boxed runtime representation, the widening
//! coercions, and `show` all agree with it.

use super::helpers::*;

#[test]
fn division_produces_an_exact_rational() {
    let out = run_subcommand("rational_show.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("3/2"),
        "expected 3 / 2 to show as 3/2, not a truncated 1:\n{}",
        out.stdout
    );
}

#[test]
fn rationals_are_normalized() {
    // `BigRational` is always gcd-reduced with a positive denominator, so a
    // whole-number rational prints bare and `-1/-2` prints as `1/2`.
    let out = run_subcommand("rational_normalizes.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("2 1/2 1/2"),
        "expected `4/2 -> 2`, `2/4 -> 1/2`, `-1/-2 -> 1/2`:\n{}",
        out.stdout
    );
}

#[test]
fn rational_arithmetic_is_exact() {
    // 1/3 + 1/6 == 1/2 exactly — the fact no floating-point representation
    // gets right, and the reason this is boxed rather than approximated.
    let out = run_subcommand("rational_arithmetic.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("1/2"),
        "expected 1/3 + 1/6 == 1/2 exactly:\n{}",
        out.stdout
    );
}

#[test]
fn int_widens_into_a_rational_position() {
    // `x + 1` where x : Rational — the Int literal widens (ℤ ⊂ ℚ), giving
    // 1/3 + 1 == 4/3.
    let out = run_subcommand("rational_widening.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("4/3"),
        "expected 1/3 + 1 == 4/3:\n{}",
        out.stdout
    );
}

#[test]
fn provably_divisible_narrows_back_to_int() {
    // `(2 * x) / 2` is proved to be an Int by the ordinary range check, so
    // the Rational narrows back at the return boundary and prints as a
    // plain integer.
    let out = run_subcommand("rational_divisible_is_int.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 21"),
        "expected (2 * 21) / 2 == 21:\n{}",
        out.stdout
    );
}

#[test]
fn comparison_and_equality_use_value_not_pointer_identity() {
    // `4/2 == 2` must hold even though the two sides are separate
    // allocations — normalization plus `cantor_rational_cmp` is what makes
    // that true.
    let out = run_subcommand("rational_comparison.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 99"),
        "expected 1/2 < 1 and 4/2 == 2:\n{}",
        out.stdout
    );
}

#[test]
fn negation_is_exact() {
    let out = run_subcommand("rational_negate.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("-1/2"),
        "expected -(1/2) == -1/2:\n{}",
        out.stdout
    );
}

#[test]
fn division_into_an_int_range_is_a_counterexample() {
    // The headline diagnostic: `a / b` is not an Int in general. The witness
    // output must render as a fraction, not as a bogus `0` — an `output = 0
    // (not in Int)` line would be self-contradictory, since 0 *is* in Int.
    let out = run_file("rational_not_int_counterexample.cantor");
    assert!(
        out.stdout.contains("counterexample"),
        "expected a counterexample for `a / b : Int`:\n{}\n{}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stdout.contains("output = 0"),
        "a rational witness must not render as 0:\n{}",
        out.stdout
    );
}

#[test]
fn quot_on_a_rational_is_a_clean_diagnostic() {
    // Euclidean division has no rational reading. This is a permanent user
    // error, so it must not surface as an internal compiler error.
    let out = run_file("rational_quot_rejected.cantor");
    assert_ne!(out.code, 0, "expected a compile error:\n{}", out.stdout);
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("integer division"),
        "expected a `quot`-on-Rational diagnostic:\n{combined}"
    );
    assert!(
        !combined.contains("internal compiler error"),
        "must be a user diagnostic, not an ICE:\n{combined}"
    );
}
