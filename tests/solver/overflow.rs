//! int-soundness-plan phase 1: per-arithmetic-node overflow obligations.
//!
//! These inspect `ConstrainedTree::overflow_checks` directly rather than
//! `CheckResult`, since an unproved overflow obligation is deliberately
//! invisible to the proved/counterexample/unknown report — it's a silent
//! side-channel consumed only by codegen (see `constrained.rs`'s doc comment).

use super::helpers::*;

fn unproved_overflow_count(src: &str) -> usize {
    check_tree(src)
        .overflow_checks
        .values()
        .filter(|proved| !**proved)
        .count()
}

#[test]
fn bounded_mul_has_no_unproved_overflow_check() {
    let n = unproved_overflow_count("mul32 : Int32 * Int32 -> Int\nmul32(x, y) = x * y");
    assert_eq!(
        n, 0,
        "Int32*Int32 multiply should be proved not to overflow i64"
    );
}

#[test]
fn unconstrained_mul_has_unproved_overflow_check() {
    let n = unproved_overflow_count("mul : Int * Int -> Int\nmul(x, y) = x * y");
    assert!(
        n >= 1,
        "unconstrained Int*Int multiply should have an unproved overflow obligation"
    );
}

#[test]
fn bounded_add_has_no_unproved_overflow_check() {
    let n = unproved_overflow_count("add32 : Int32 * Int32 -> Int\nadd32(x, y) = x + y");
    assert_eq!(n, 0, "Int32*Int32 add should be proved not to overflow i64");
}

#[test]
fn unconstrained_sub_has_unproved_overflow_check() {
    let n = unproved_overflow_count("sub : Int * Int -> Int\nsub(x, y) = x - y");
    assert!(
        n >= 1,
        "unconstrained Int - Int should have an unproved overflow obligation"
    );
}

#[test]
fn negation_of_bounded_int_has_no_unproved_overflow_check() {
    let n = unproved_overflow_count("neg32 : Int32 -> Int\nneg32(x) = -x");
    assert_eq!(
        n, 0,
        "negating an Int32 should be proved not to overflow i64"
    );
}

#[test]
fn negation_of_unconstrained_int_has_unproved_overflow_check() {
    let n = unproved_overflow_count("neg : Int -> Int\nneg(x) = -x");
    assert!(
        n >= 1,
        "negating an unconstrained Int should have an unproved overflow obligation (i64::MIN)"
    );
}

#[test]
fn unconstrained_division_has_unproved_overflow_check() {
    // i64::MIN / -1 isn't excluded by this domain, so the MIN/-1 overflow
    // obligation should remain unproved even though divisor-nonzero is fine.
    let n = unproved_overflow_count("safe_div : Int * (Int - {0}) -> Int\nsafe_div(x, y) = x / y");
    assert!(
        n >= 1,
        "unconstrained safe division should still have an unproved MIN/-1 overflow obligation"
    );
}

#[test]
fn divisor_nonzero_still_a_hard_gate_alongside_overflow_channel() {
    // Regression: the new overflow channel must not weaken or interfere with
    // the existing (unrelated) divisor-nonzero obligation, which stays a hard
    // proof gate untouched by this phase.
    counterexample("bad_div : Int * Int -> Int\nbad_div(x, y) = x / y");
}
