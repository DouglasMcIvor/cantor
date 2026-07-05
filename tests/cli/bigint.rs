//! int-soundness-plan phase 3 step 4b — tagged-value codegen, end to end.
//! Complements overflow.rs (arithmetic promotion) with the other surfaces
//! that needed tag-awareness: comparisons, call boundaries between raw and
//! tagged representations, runtime overload dispatch mixing an Int64/BigInt
//! split, and domain-membership checks.

use super::helpers::*;

#[test]
fn comparison_on_boxed_value_is_correct() {
    let out = run_subcommand("bigint_compare.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected huge() > i64::MAX to be true:\n{}",
        out.stdout
    );
}

#[test]
fn call_boundary_between_promoted_and_tagged_function_is_correct() {
    // add8(3, 4) = 7, computed on the raw Int64 fast path (Step A promotion);
    // combine(100) = 7 + 100 = 107, computed on the tagged path — the raw
    // result must be tagged before combining with the tagged local.
    let out = run_subcommand("bigint_call_boundary.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 107"),
        "expected 107:\n{}",
        out.stdout
    );
}

#[test]
fn runtime_dispatch_to_bigint_candidate_is_correct() {
    // caller(y) = f(y) is an unresolved dispatch (y not statically known) —
    // a genuinely boxed argument must dispatch to the BigInt candidate and
    // round-trip correctly through the phi merge.
    let out = run_subcommand("bigint_dispatch.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 9223372036854775808"),
        "expected the exact boxed value to round-trip:\n{}",
        out.stdout
    );
}

#[test]
fn runtime_dispatch_to_int64_candidate_is_correct() {
    let out = run_subcommand("bigint_dispatch_small.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected the small value to round-trip:\n{}",
        out.stdout
    );
}

#[test]
fn nat_membership_on_boxed_positive_value_is_true() {
    let out = run_subcommand("bigint_membership.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected a huge positive value to be in Nat:\n{}",
        out.stdout
    );
}

#[test]
fn nat_membership_on_boxed_negative_value_is_false() {
    let out = run_subcommand("bigint_membership_negative.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 0"),
        "expected a huge negative value to not be in Nat:\n{}",
        out.stdout
    );
}

#[test]
fn bigint_named_set_membership_true_for_boxed_value() {
    // BigInt = Int - Int64, exposed as an ordinary named set purely for
    // `in`/`not in` checks (assert/require).
    let out = run_subcommand("bigint_named_set.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected i64::MAX + 1 to be in BigInt:\n{}",
        out.stdout
    );
}

#[test]
fn bigint_named_set_membership_false_for_small_value() {
    let out = run_subcommand("bigint_named_set_small.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 0"),
        "expected a small value to not be in BigInt:\n{}",
        out.stdout
    );
}
