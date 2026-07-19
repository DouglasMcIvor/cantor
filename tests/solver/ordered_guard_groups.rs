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
fn ordered_group_calls_never_get_a_static_overload_resolution_entry() {
    // `decide_overload_resolutions`'s static-resolution shortcut ("is
    // `path_cond → candidate_i`'s domain provable, tried in order") is
    // sound for a hand-written disjoint overload set: if every value
    // reaching a call site is provably in candidate i's domain, no other
    // candidate could ever also match, so "first provable" and "first
    // match" agree. That equivalence breaks for an ordered guard group,
    // where domains may deliberately overlap — a later/wildcard arm's
    // domain being unconditionally provable does *not* mean it's the
    // first-declared match for every value (an earlier arm this loop
    // already skipped, for not being provable *unconditionally*, could
    // still be the correct match for *some* reaching values). So
    // `encode_call.rs` deliberately never records a resolution for an
    // ordered-group call — it always falls back to the runtime dispatch
    // chain instead, which correctly respects declaration order (see
    // `tests/cli/ordered_guard_groups.rs::
    // ordered_guard_group_runtime_dispatch_respects_declaration_order` for
    // the end-to-end proof this actually produces the right value).
    let tree = check_tree(
        "classify : Int -> Int\n\
         classify(x for x >= 0) = 1\n\
         classify(x for x > 5) = 2\n\
         classify(_) = 3\n\
         caller : -> Int\n\
         caller() = classify(10)",
    );
    assert!(
        tree.overload_resolution.is_empty(),
        "expected no static overload_resolution entry for an ordered-group call \
         (deferred optimization — see TODO in encode_call.rs), got {:?}",
        tree.overload_resolution
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
