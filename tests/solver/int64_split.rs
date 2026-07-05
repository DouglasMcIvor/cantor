//! int-soundness-plan phase 3: the compiler-generated `Int64`/`BigInt`
//! overload split (step 4a) and whole-function `Int64` promotion (step A).
//! See `src/solver/int64_split.rs`'s module doc and
//! docs/int-soundness-plan.md's "The overload split" / "Tagging scope"
//! sections.

use cantor::kind::Kind;
use cantor::semantics::tree::SemItem;

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

/// The (param_kinds, return_kind) of the sole `FunctionDef` named `name` in
/// a checked tree — panics if there isn't exactly one (a split/overload
/// group has no single answer, and tests using this helper aren't expected
/// to hit one).
fn kinds_of(tree: &cantor::solver::ConstrainedTree, name: &str) -> (Vec<Kind>, Kind) {
    let mut matches = tree.sem_items.iter().filter_map(|item| match item {
        SemItem::FunctionDef(def) if def.name.0 == name => {
            Some((def.param_kinds.clone(), def.return_kind.clone()))
        }
        _ => None,
    });
    let result = matches
        .next()
        .unwrap_or_else(|| panic!("no FunctionDef named `{name}`"));
    assert!(
        matches.next().is_none(),
        "expected exactly one FunctionDef named `{name}`"
    );
    result
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

// ── Step A: whole-function Int64 promotion ──────────────────────────────

#[test]
fn bounded_int8_domain_promotes_without_split() {
    // Int8 ⊆ Int64, and there's no "otherwise" case any caller could ever
    // hit, so this should promote in place — one item, no BigInt sibling.
    let results = check_all("f : Int8 -> Int8\nf(x) = x");
    assert_eq!(
        names_for(&results, "f"),
        1,
        "a bounded-domain function must not split, got {results:?}"
    );
    let tree = check_tree("f : Int8 -> Int8\nf(x) = x");
    assert_eq!(
        kinds_of(&tree, "f"),
        (vec![Kind::Int64], Kind::Int64),
        "expected `f` to be promoted to raw Kind::Int64"
    );
}

#[test]
fn bounded_multi_param_domain_promotes() {
    // Both parameters individually ⊆ Int64, and `x + y` under two Int8
    // operands can't leave Int64 — every per-node overflow obligation
    // should prove, same as the single-param case.
    let tree = check_tree("f : Int8 * Int8 -> Int16\nf(x, y) = x + y");
    assert_eq!(
        kinds_of(&tree, "f"),
        (vec![Kind::Int64, Kind::Int64], Kind::Int64),
        "expected both parameters and the return to promote to Kind::Int64"
    );
}

#[test]
fn zero_param_bounded_range_promotes() {
    // No parameters to bound at all (vacuously eligible); a literal return
    // is always already representable in i64 (the lexer already rejects
    // out-of-i64 literals), so this should promote too.
    let tree = check_tree("f : -> Int8\nf() = 5");
    assert_eq!(
        kinds_of(&tree, "f"),
        (vec![], Kind::Int64),
        "expected a zero-param function to promote"
    );
}

#[test]
fn unbounded_nat_domain_does_not_promote() {
    // Nat is unbounded above — not a subset of Int64 — so this must stay
    // plain Kind::Int, exactly as before Step A existed.
    let tree = check_tree("f : Nat -> Int\nf(x) = x");
    assert_eq!(
        kinds_of(&tree, "f"),
        (vec![Kind::Int], Kind::Int),
        "a Nat-domain function must not be promoted"
    );
}

#[test]
fn int64_domain_that_can_overflow_does_not_promote() {
    // The domain itself (Int64) is trivially ⊆ Int64, but `x + x` can
    // overflow i64 for large `x` — the per-node overflow obligation for
    // this Add must fail to prove, so promotion must decline even though
    // the outer `domain -> range` contract (Int64 -> Int, unbounded) holds
    // trivially. This is exactly the gap a "final result in range alone"
    // check would miss.
    let tree = check_tree("f : Int64 -> Int\nf(x) = x + x");
    assert_eq!(
        kinds_of(&tree, "f"),
        (vec![Kind::Int], Kind::Int),
        "a function whose body can overflow i64 must not be promoted"
    );
}

#[test]
fn promoted_function_callers_still_prove() {
    // A promoted callee should be entirely transparent to callers — no
    // overload set, no dispatch, just an ordinary direct call, and the file
    // should still fully prove.
    proved_all(
        "f : Int8 -> Int8\n\
         f(x) = x\n\
         caller : Int8 -> Int8\n\
         caller(x) = f(x)",
    );
}
