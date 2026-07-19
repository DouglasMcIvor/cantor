//! Ordered guard groups: a signature followed directly by 2+ bodies with no
//! repeated signature line between them. Arms are tried in declaration
//! order (first match wins), skipping pairwise disjointness in favor of a
//! coverage obligation — see `solver::disjointness::check_ordered_group_coverage`.

use super::helpers::*;

#[test]
fn ordered_group_with_wildcard_catchall_is_proved_without_solver_gap() {
    // The trailing `_` arm makes coverage trivially provable — no live SMT
    // question, no solver instantiated at all for the coverage obligation.
    proved_all(
        "sign : Int -> Int\n\
         sign(x for x < 0) = -x\n\
         sign(x for x > 0) = x\n\
         sign(_) = 0",
    );
}

#[test]
fn ordered_group_missing_coverage_is_rejected_with_witness() {
    // No `_`, and the guards leave a gap at 3, 4, 5 — coverage must fail
    // with a witness, not silently pass.
    let results = check_all(
        "f : Nat -> Nat\n\
         f(x for x < 3) = 0\n\
         f(x for x > 5) = 1",
    );
    let coverage = results
        .iter()
        .filter(|(name, _)| name == "f")
        .flat_map(|(_, sig_results)| sig_results)
        .find(|(label, _)| label.contains("ordered guard group"));
    let Some((_, result)) = coverage else {
        panic!("expected an ordered guard group coverage result entry, got {results:?}");
    };
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "expected a coverage gap to be rejected with a witness, got {result:?}"
    );
}

#[test]
fn ordered_group_fully_covered_by_explicit_guards_no_wildcard_is_proved() {
    // No `_` at all — every arm has an explicit guard, but together they
    // still cover the whole declared `Int` domain. Exercises the general
    // (non-trivial-skip) coverage proof, not just the wildcard fast path.
    proved_all(
        "sign : Int -> Int\n\
         sign(x for x < 0) = -x\n\
         sign(x for x == 0) = 0\n\
         sign(x for x > 0) = x",
    );
}

#[test]
fn wildcard_must_cover_every_param_to_trivially_skip() {
    // Only the *second* param of the last arm is `_` — the first still has
    // a real guard, so the trivial-skip condition ("all params of the last
    // arm are wildcards") does not fire, and a real proof is needed (and
    // obtained: `x < 0` and `x >= 0` alone already cover every `x`,
    // regardless of `y`, so the two arms together do cover `Int * Int`).
    proved_all(
        "f : Int * Int -> Int\n\
         f(x for x < 0, _) = 0\n\
         f(x for x >= 0, _) = 1",
    );
}

#[test]
fn overload_resolution_prefers_first_matching_arm_in_ordered_group() {
    // Deliberately overlapping domains (`x >= 0` is a superset of `x > 5`) —
    // legal in an ordered group precisely because order resolves the
    // ambiguity. `n = 10` satisfies both arms; the first-declared one must
    // win.
    let tree = check_tree(
        "classify : Int -> Int\n\
         classify(x for x >= 0) = 1\n\
         classify(x for x > 5) = 2\n\
         classify(_) = 3\n\
         caller : -> Int\n\
         caller() = classify(10)",
    );
    assert_eq!(
        tree.overload_resolution.len(),
        1,
        "expected exactly one resolved call site, got {:?}",
        tree.overload_resolution
    );
    let resolved_idx = *tree.overload_resolution.values().next().unwrap();
    assert_eq!(
        resolved_idx, 0,
        "a value matching more than one arm must resolve to the first-declared one"
    );
}

#[test]
fn unsupported_domain_shape_in_ordered_group_reports_unknown_not_a_false_proof() {
    // A `Vector(Int)` parameter position isn't yet supported by the
    // overload-disjointness/coverage SMT encoding (`fresh_overload_param_-
    // terms`'s non-scalar-position catch-all). No wildcard arm, so the
    // trivial-skip never fires and a real (here, unsupported) proof is
    // attempted — must report Unknown, never a silent/false Proved.
    let results = check_all(
        "f : Int* -> Int\n\
         f(x for len(x) > 0) = 1\n\
         f(x for len(x) == 0) = 0",
    );
    let coverage = results
        .iter()
        .filter(|(name, _)| name == "f")
        .flat_map(|(_, sig_results)| sig_results)
        .find(|(label, _)| label.contains("ordered guard group"));
    let Some((_, result)) = coverage else {
        panic!("expected an ordered guard group coverage result entry, got {results:?}");
    };
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "expected an unsupported domain shape to report Unknown, got {result:?}"
    );
}
