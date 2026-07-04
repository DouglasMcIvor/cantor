//! int-soundness-plan phase 2: function overloading with multiple bodies —
//! solver-level disjointness obligations and call-resolution recording.

use super::helpers::*;

#[test]
fn disjoint_domain_overloads_are_proved() {
    proved_all(
        "classify : Nat -> Int\n\
         classify(x) = x\n\
         classify : Int - Nat -> Int\n\
         classify(x) = -x",
    );
}

#[test]
fn overlapping_domain_overloads_are_rejected_with_witness() {
    let results = check_all(
        "over : Int -> Int\n\
         over(x) = x\n\
         over : Nat -> Int\n\
         over(x) = x + 1",
    );
    // Multiple entries share the key "over" (one per `FunctionDef`, plus the
    // disjointness check) — search across all of them, not just the first.
    let disjointness = results
        .iter()
        .filter(|(name, _)| name == "over")
        .flat_map(|(_, sig_results)| sig_results)
        .find(|(label, _)| label.contains("disjointness"));
    let Some((_, result)) = disjointness else {
        panic!("expected a disjointness result entry, got {results:?}");
    };
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "expected overlapping domains to be rejected with a witness, got {result:?}"
    );
}

#[test]
fn different_arity_overloads_need_no_disjointness_check() {
    // `poly`'s two overloads have overlapping-looking domains (`Int` covers
    // everything a 2-arg call could also see) but different arity — arity
    // alone already makes them disjoint, no solver call should even be
    // needed, and the file must still be fully proved.
    proved_all(
        "poly : Int -> Int\n\
         poly(x) = x\n\
         poly : Int * Int -> Int\n\
         poly(x, y) = x + y",
    );
}

#[test]
fn statically_resolvable_call_is_recorded_in_overload_resolution() {
    let tree = check_tree(
        "classify : Nat -> Int\n\
         classify(x) = x\n\
         classify : Int - Nat -> Int\n\
         classify(x) = -x\n\
         caller : Nat -> Int\n\
         caller(n) = classify(n)",
    );
    assert_eq!(
        tree.overload_resolution.len(),
        1,
        "expected exactly one resolved call site, got {:?}",
        tree.overload_resolution
    );
    // `n : Nat` provably lies in the first-declared overload's domain (Nat),
    // which is overload index 0 (file order among `classify`'s definitions).
    let resolved_idx = *tree.overload_resolution.values().next().unwrap();
    assert_eq!(resolved_idx, 0);
}

#[test]
fn unresolvable_call_is_absent_from_overload_resolution() {
    // `x : Int` is unconstrained — the caller can't prove membership in
    // either of `classify`'s disjoint sub-domains, so the call must fall
    // back to runtime dispatch (no entry recorded), while the file as a
    // whole still proves (the domain-union obligation `x ∈ Nat ∪ (Int-Nat)`
    // holds trivially since that union is all of `Int`).
    let tree = check_tree(
        "classify : Nat -> Int\n\
         classify(x) = x\n\
         classify : Int - Nat -> Int\n\
         classify(x) = -x\n\
         caller : Int -> Int\n\
         caller(x) = classify(x)",
    );
    assert!(
        tree.overload_resolution.is_empty(),
        "expected no resolved call site for an unconstrained argument, got {:?}",
        tree.overload_resolution
    );
}
