//! int-soundness-plan phase 3, step 4a: the compiler-generated `Int64`/
//! `BigInt` overload split — solver-gated, MVP scope (single parameter,
//! single signature, bare `Int -> Int`). See `src/solver/int64_split.rs`'s
//! module doc and docs/int-soundness-plan.md's "The overload split" section.

use super::helpers::*;

/// Counts entries for `name` that are genuine per-`FunctionDef` check
/// results — excludes the synthetic "disjointness" pair-check entries
/// `check_overload_disjointness` adds under the same name whenever a group
/// has more than one member (split or ordinary user overloading alike).
fn names_for(results: &[(String, Vec<(String, CheckResult)>)], name: &str) -> usize {
    results
        .iter()
        .filter(|(n, sig_results)| {
            n == name && !sig_results.iter().any(|(label, _)| label.contains("disjointness"))
        })
        .count()
}

#[test]
fn bare_int_identity_splits_into_two_proved_overloads() {
    let results = check_all("f : Int -> Int\nf(x) = x");
    assert_eq!(
        names_for(&results, "f"),
        2,
        "expected the Int64/BigInt split, got {results:?}"
    );
    for (name, sig_results) in &results {
        if name != "f" {
            continue;
        }
        for (label, result) in sig_results {
            assert_eq!(result, &CheckResult::Proved, "`{label}` should be Proved");
        }
    }
}

#[test]
fn growing_function_does_not_split_but_file_still_proves() {
    // `x + x` can't prove `Int64 -> Int64` (x near i64::MAX overflows) — no
    // split should be generated, and the file must still fully prove:
    // range obligations don't require Int64-boundedness, only the
    // separate phase 1 overflow side-channel does, and that never gates
    // `all_proved` (see solver/mod.rs's comment on `overflow_checks`).
    //
    // Deliberately linear (`+`, not `*`): `x * x` hits an unrelated,
    // pre-existing cvc5 hang on self-multiplication (see
    // int-soundness-plan.md's "Known issues" — reproduces independent of
    // this split, so it's out of scope here, but it means this test must
    // avoid it too, not just `try_split`'s own `Mul` guard).
    let results = check_all("f : Int -> Int\nf(x) = x + x");
    assert_eq!(
        names_for(&results, "f"),
        1,
        "a genuinely growing function must not be split, got {results:?}"
    );
    proved_all("f : Int -> Int\nf(x) = x + x");
}

#[test]
fn non_bare_int_domain_does_not_split() {
    // `Nat` isn't the bare `Int` builtin the MVP eligibility check requires,
    // even though every `Nat` value is also an `Int` value.
    let results = check_all("f : Nat -> Int\nf(x) = x");
    assert_eq!(
        names_for(&results, "f"),
        1,
        "a non-bare-Int domain must not be split, got {results:?}"
    );
}

#[test]
fn multi_signature_function_does_not_split() {
    // The MVP restricts eligibility to exactly one signature — a function
    // using the pre-existing multiple-signatures-one-body feature (even if
    // every signature individually looks Int64-eligible) is out of scope
    // for this first cut.
    let results = check_all("f : Int -> Int\nf : Int -> Int\nf(x) = x");
    assert_eq!(
        names_for(&results, "f"),
        1,
        "a multi-signature function must not be split, got {results:?}"
    );
}

#[test]
fn already_overloaded_name_is_left_alone() {
    // `over`'s first overload (`Int -> Int`, identity-shaped body) would be
    // individually split-eligible, but `over` already has a second,
    // user-written overload in the file — the MVP leaves any name with a
    // pre-existing overload sibling untouched entirely (see
    // `generate_int64_bigint_splits`'s doc comment) rather than reasoning
    // about a 3-way disjointness group. Mirrors
    // `overloads::overlapping_domain_overloads_are_rejected_with_witness`,
    // which depends on this *not* transforming `over`'s first overload.
    let results = check_all(
        "over : Int -> Int\n\
         over(x) = x\n\
         over : Nat -> Int\n\
         over(x) = x + 1",
    );
    assert_eq!(
        names_for(&results, "over"),
        2,
        "a name with a pre-existing user overload must not be split, got {results:?}"
    );
}

#[test]
fn recursive_int64_preserving_function_splits_via_narrowed_induction_hypothesis() {
    // Halving strictly shrinks magnitude, so `x / 2` never leaves `Int64`
    // once `x` is already inside it — but proving that *for the recursive
    // call* requires using the narrowed `Int64 -> Int64` contract as the
    // induction hypothesis. If the self-call instead resolved against the
    // original wide `Int -> Int` contract (interprocedural checking treats
    // calls opaquely, never inlining), the recursive result would only be
    // known to lie in `Int`, and the `Int64` claim would NOT prove. This
    // test is the one that actually exercises `try_split`'s `trial_env`
    // self-entry override, not just the eligibility shape-matching.
    let results = check_all(
        "half_count : Int -> Int\n\
         half_count(x) = if x == 0 then 0 else half_count(x / 2)",
    );
    assert_eq!(
        names_for(&results, "half_count"),
        2,
        "expected the recursive function to split, got {results:?}"
    );
}

#[test]
fn split_overloads_dispatch_like_an_ordinary_phase_2_pair() {
    // A literal argument provably within Int64 should statically resolve
    // to the Int64 overload — exactly phase 2's existing dispatch
    // machinery, exercised transparently over a compiler-generated pair
    // instead of a user-written one. `caller` takes no parameters so it
    // can't itself be split-eligible (MVP requires exactly one parameter),
    // keeping this test focused on the callee's split.
    let tree = check_tree(
        "f : Int -> Int\n\
         f(x) = x\n\
         caller : -> Int\n\
         caller() = f(5)",
    );
    assert_eq!(
        tree.overload_resolution.len(),
        1,
        "expected exactly one resolved call site, got {:?}",
        tree.overload_resolution
    );
    let resolved_idx = *tree.overload_resolution.values().next().unwrap();
    // File order: the Int64 overload is synthesized (and pushed) before
    // the BigInt fallback — see `generate_int64_bigint_splits`.
    assert_eq!(resolved_idx, 0);
}
