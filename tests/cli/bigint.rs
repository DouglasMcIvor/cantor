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

// ── Small-value membership regression (found in review, 2026-07-05; fixed) ──
//
// `bigint_named_set_membership_{true,false}_for_*` above both use a bare
// `Int -> Int` signature -- which, unbeknownst to those tests, is exactly
// `int64_split`'s auto-split eligibility shape (`try_split`, single param,
// bare `Int` domain and range, no `Mul`). Both fixtures' `classify` gets
// silently rewritten into a compiler-generated `Int64`/`BigInt` overload
// pair, and the call site's literal argument statically resolves to one
// specific candidate -- so neither test ever actually exercised the tagged,
// non-split membership-check codegen path they were written to cover.
//
// Once a *non*-splittable signature (`Int -> Bool` here) is used instead, a
// real bug surfaced: `compile_int_cmp_const` (src/codegen/membership.rs)
// decided whether to use the raw bit-pattern comparison or the tag-aware
// `cantor_bigint_cmp` one by checking only the *value being tested*'s tag
// bit, never the constant it's compared against. `Int64`'s own bound
// (`i64::MIN`/`i64::MAX`) and `BigInt`'s (the same pair, complemented) both
// lie outside the tagged scheme's small-int range, so the bound itself got
// boxed (a fresh heap pointer) at every check. For an ordinary *small*,
// unboxed `x`, the code picked the raw-bit-pattern branch and ended up
// comparing `x`'s small encoding directly against that pointer's numeric
// value -- garbage, not a real magnitude comparison.
//
// Fixed: `compile_int_cmp_const` now branches on whether the *constant* `k`
// itself needs boxing (knowable at compile time, unlike `val`'s tag bit) —
// when it does, the comparison unconditionally uses the tag-aware
// `cantor_bigint_cmp` path and skips the raw/`select` path entirely, since
// that path is only ever correct when `k` itself is small.
//
// This wasn't a rare corner case: it broke `Int64`/`BigInt` named-set
// membership for the *ordinary*, non-huge values that are the overwhelming
// common case, and it was silent -- no abort, just a wrong boolean answer
// flowing on into whatever `assert`/`if` used it. It also risked silently
// mis-dispatching `int64_split`'s own runtime overload-dispatch chain
// (`compile_overload_domain_match` calls the same tag-aware-membership
// code for the `Int64` candidate's domain check) -- not separately
// reproduced here because `try_split` always gives both candidates the
// exact same body, so a wrongly-chosen candidate is unobservable unless the
// two candidates' raw-vs-tagged arithmetic itself diverges (e.g. via
// overflow); the standalone repro above is the clean, minimal one.
mod small_value_membership_regression {
    use super::*;

    #[test]
    fn int64_membership_is_true_for_an_ordinary_small_value() {
        let out = run_subcommand("int64_membership_small_value.cantor");
        assert_eq!(
            out.code, 0,
            "expected exit 0:\n{}\n{}",
            out.stdout, out.stderr
        );
        assert!(
            out.stdout.contains("main() = 1"),
            "100 is trivially in Int64:\n{}",
            out.stdout
        );
    }

    #[test]
    fn bigint_membership_is_false_for_an_ordinary_small_value() {
        let out = run_subcommand("bigint_membership_small_value.cantor");
        assert_eq!(
            out.code, 0,
            "expected exit 0:\n{}\n{}",
            out.stdout, out.stderr
        );
        assert!(
            out.stdout.contains("main() = 0"),
            "100 is not in BigInt:\n{}",
            out.stdout
        );
    }
}

// ── Container elements (found in review, 2026-07-05; Vector(Int) fixed) ────
//
// `Vector(Int)`/`Set(Int)` elements were documented as out of scope for
// BigInt (int-soundness-plan.md step 4b): a boxed element aborted via
// `ensure_raw_int64` rather than computing the correct answer. Fixed for
// `Vector(Int)` by no longer decoding/re-encoding at the vector push/read
// boundary at all — `Int64Array` storage is representation-agnostic, so a
// tagged (possibly boxed) word round-trips through it unchanged; `Tuple`/
// `TaggedUnion` element storage already worked this way. `Set(Int)` needs a
// canonical/deduped comparison (two different boxed allocations holding the
// same value must still dedup to one set entry) and is still open — see
// `int64_split`'s sibling module or int-soundness-plan.md for that follow-up.
#[test]
fn vector_of_int_holding_a_boxed_element_reads_back_correctly() {
    let out = run_subcommand("vector_int_bigint_element.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 9223372036854775808"),
        "expected the boxed element to read back exactly:\n{}",
        out.stdout
    );
}
