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

// ── Known issues (found in review, 2026-07-05) ──────────────────────────────
//
// `bigint_named_set_membership_{true,false}_for_*` above both use a bare
// `Int -> Int` signature -- which, unbeknownst to those tests, is exactly
// `int64_split`'s auto-split eligibility shape (`try_split`, single param,
// bare `Int` domain and range, no `Mul`). Both fixtures' `classify` gets
// silently rewritten into a compiler-generated `Int64`/`BigInt` overload
// pair, and the call site's literal argument statically resolves to one
// specific candidate -- so neither test ever actually exercises the tagged,
// non-split membership-check codegen path they were written to cover.
//
// Once a *non*-splittable signature (`Int -> Bool` here) is used instead, a
// real bug surfaces: `compile_int_cmp_const` (src/codegen/membership.rs)
// decides whether to use the raw bit-pattern comparison or the tag-aware
// `cantor_bigint_cmp` one by checking only the *value being tested*'s tag
// bit, never the constant it's compared against. `Int64`'s own bound
// (`i64::MIN`/`i64::MAX`) and `BigInt`'s (the same pair, complemented) both
// lie outside the tagged scheme's small-int range, so the bound itself gets
// boxed (a fresh heap pointer) at every check. For an ordinary *small*,
// unboxed `x`, the code picks the raw-bit-pattern branch and ends up
// comparing `x`'s small encoding directly against that pointer's numeric
// value -- garbage, not a real magnitude comparison.
//
// Root cause and fix, precisely: `compile_int_cmp_const`'s `is_boxed` check
// only inspects `val`'s tag bit; it needs to also account for whether the
// *constant* `k` requires boxing (`encode_small(k)` -- knowable at compile
// time, unlike `val`'s tag bit). When `k` is outside the small range, the
// comparison must unconditionally use the tag-aware `cantor_bigint_cmp`
// path; the raw/select path is only ever correct when `k` itself is small.
//
// This isn't a rare corner case: it breaks `Int64`/`BigInt` named-set
// membership for the *ordinary*, non-huge values that are the overwhelming
// common case, and it's silent -- no abort, just a wrong boolean answer
// flowing on into whatever `assert`/`if` used it. It also risks silently
// mis-dispatching `int64_split`'s own runtime overload-dispatch chain
// (`compile_overload_domain_match` calls the same tag-aware-membership
// code for the `Int64` candidate's domain check) -- not separately
// reproduced here because `try_split` always gives both candidates the
// exact same body, so a wrongly-chosen candidate is unobservable unless the
// two candidates' raw-vs-tagged arithmetic itself diverges (e.g. via
// overflow); the standalone repro above is the clean, minimal one.
mod known_issues {
    use super::*;

    #[test]
    #[ignore = "compile_int_cmp_const only checks val's tag bit, not the \
                compared constant's -- Int64's own bound needs boxing, so a \
                small, non-split `Int -> Bool` check of `x in Int64` wrongly \
                returns false for x = 100; see this module's doc comment"]
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
    #[ignore = "same root cause as int64_membership_is_true_for_an_ordinary_small_value \
                (the complementary Outside bound), reached via a non-split \
                `Int -> Bool` check of `x in BigInt` -- wrongly returns true \
                for x = 100; see this module's doc comment"]
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

    #[test]
    #[ignore = "Vector(Int)/Set(Int) elements are documented as out of scope \
                for BigInt (int-soundness-plan.md step 4b) -- a boxed element \
                currently aborts via ensure_raw_int64 (\"compiler invariant \
                violated\", a misleading message for what is really an \
                unimplemented feature, not a compiler bug) rather than \
                computing the correct answer. Fails loudly, per CLAUDE.md, so \
                this is a completeness gap rather than a soundness one -- but \
                still open."]
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
}
