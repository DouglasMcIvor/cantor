//! `rem`/`quot` — Euclidean remainder/quotient, end to end. See
//! docs/wrapping-and-quotient-sets-plan.md, step 1 ("Prerequisite: `rem`/
//! `quot` operators").
//!
//! Fixtures route the computation through an `Int32`-domain helper function
//! (Step A whole-function promotion to raw `Kind::Int64`, int-soundness-plan
//! phase 3) rather than calling `rem`/`quot` on a bare `Int` directly: an
//! unbounded `Int` operand hits the deliberate `Unsupported` compile error
//! this slice adds (see `rem_on_unbounded_int_is_a_clean_compile_error`
//! below) since no `cantor_bigint_rem`/`cantor_bigint_quot` runtime function
//! exists yet.
//!
//! `main`'s return type is deliberately a bare `-> Int` (not `Int | Fail`,
//! not a tuple) in every correctness fixture here — a promoted call's raw
//! `Int64` result flowing directly into a `Fail`-wire success payload or a
//! tuple leaf turned out to hit a separate, pre-existing display/coercion
//! bug (confirmed with `/` too, not introduced by this feature): the value
//! reaches the runtime untagged but `format_tagged_int`/`cantor_bigint_*`
//! assume it's tagged, corrupting the printed value or crashing outright.
//! Flagged to Doug for separate follow-up; every fixture below avoids it by
//! sticking to the one shape that's confirmed to tag correctly.

use super::helpers::*;

#[test]
fn rem_euclidean_negative_dividend() {
    // -7 rem 5 == 3 (the motivating example's headline fact).
    let out = run_subcommand("rem_quot_neg_dividend.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3"),
        "expected -7 rem 5 == 3:\n{}",
        out.stdout
    );
}

#[test]
fn quot_euclidean_negative_dividend() {
    // -7 quot 5 == -2 (paired with the rem fact above).
    let out = run_subcommand("quot_neg_dividend.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = -2"),
        "expected -7 quot 5 == -2:\n{}",
        out.stdout
    );
}

#[test]
fn rem_euclidean_negative_divisor() {
    // 7 rem -5 == 2 — Euclidean rem is always non-negative regardless of
    // the divisor's sign, unlike a negative-dividend result being corrected
    // by adding the divisor's magnitude.
    let out = run_subcommand("rem_neg_divisor.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 2"),
        "expected 7 rem -5 == 2:\n{}",
        out.stdout
    );
}

#[test]
fn quot_euclidean_negative_divisor() {
    // 7 quot -5 == -1.
    let out = run_subcommand("quot_neg_divisor.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = -1"),
        "expected 7 quot -5 == -1:\n{}",
        out.stdout
    );
}

#[test]
fn rem_and_quot_reject_zero_divisor() {
    // Both operators share `/`'s domain shape: divisor must be Int AND
    // NonZeroInt. A caller passing a literal 0 to a domain that already
    // excludes it is a call-site counterexample, mirroring
    // `call_domain_violation.cantor`'s existing `/` test.
    let out = run_file("rem_quot_by_zero.cantor");
    assert_ne!(out.code, 0, "should refuse to run:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  bad_rem"),
        "expected a counterexample for bad_rem:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  bad_quot"),
        "expected a counterexample for bad_quot:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected a domain-violation reason:\n{}",
        out.stdout
    );
}

#[test]
fn rem_has_no_set_position_meaning() {
    // Unlike `+ - * /`, `rem`/`quot` have no set-forming dual — using one to
    // define a set is a hard user error (`InvalidSetExpression`), not an ICE
    // and not a silent Kind::Int default.
    let out = run_file("rem_set_position_rejected.cantor");
    assert_ne!(out.code, 0, "should be rejected:\n{}", out.stdout);
    assert!(
        out.stderr.contains("has no set-forming meaning"),
        "expected the set-position diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must be a clean diagnostic, not an ICE:\n{}",
        out.stderr
    );
}

#[test]
fn rem_on_unbounded_int_is_a_clean_compile_error() {
    // TODO(rem/quot BigInt support, docs/wrapping-and-quotient-sets-plan.md):
    // no cantor_bigint_rem/cantor_bigint_quot runtime function exists yet.
    // A bounded (Int32-promotable) domain works (see the fixtures above);
    // a bare, unbounded `Int` operand is a clean `Unsupported` compile
    // error instead of silently computing plain-i64 semantics on a value
    // that might actually be a boxed BigInt pointer.
    let out = run_subcommand("rem_unbounded_int_unsupported.cantor");
    assert_ne!(out.code, 0, "should refuse to compile:\n{}", out.stdout);
    assert!(
        out.stderr.contains("not yet supported") && out.stderr.contains("cantor_bigint_rem"),
        "expected the Unsupported/not-yet-implemented diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must be a clean diagnostic, not an ICE:\n{}",
        out.stderr
    );
}
