//! End-to-end pin for higher-order functions v0 (backlog.md): `Domain ->
//! Range` as a Kind, calling through a function-Kind parameter is checked
//! against its declared contract inside the callee's own body, AND — the
//! call-site half — a caller passing a concrete function in is checked
//! structurally against that same declared contract
//! (`solver::encode_hof::function_value_arg_membership`). Together these
//! close the soundness story end to end: `apply(double, 5)` is now
//! genuinely `proved`, a real mismatch is a real counterexample, and an
//! overloaded-function argument (not yet comparable structurally — its
//! candidates agree on Kind, not on their individually declared domain
//! Sets) stays an honest `unknown`, never a false `proved`.

use super::helpers::*;

#[test]
fn higher_order_function_program_does_not_crash() {
    let out = run_file("higher_order_functions_v0.cantor");
    assert!(
        !out.stdout.contains("panicked"),
        "must not panic:\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
    assert!(
        !out.stderr.contains("panicked"),
        "must not panic:\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
fn plain_first_order_function_in_the_same_file_still_proves() {
    // `double` itself has nothing to do with function values — its own
    // proof must be unaffected by `apply`/`main` further down the file.
    let out = run_file("higher_order_functions_v0.cantor");
    assert!(
        out.stdout.contains("proved          double"),
        "expected double proved:\n{}",
        out.stdout
    );
}

#[test]
fn calling_through_a_function_kind_param_is_provable() {
    // `apply(f, x) = f(x)` is checked against `f`'s own declared contract
    // `(Int -> Int)`, taken from `apply`'s own signature — a genuine proof,
    // not just a Kind check.
    let out = run_file("higher_order_functions_v0.cantor");
    assert!(
        out.stdout.contains("proved          apply"),
        "expected apply proved:\n{}",
        out.stdout
    );
}

#[test]
fn call_site_passing_a_matching_concrete_function_is_now_provable() {
    // `main` passes `double` (declared `Int -> Int`, exactly matching
    // `apply`'s declared `f : (Int -> Int)`) — the call-site structural
    // check closes the loop, so this is now genuinely `proved`, not just
    // Kind-checked or left `unknown`.
    let out = run_file("higher_order_functions_v0.cantor");
    assert!(
        out.stdout.contains("proved          main"),
        "expected main proved:\n{}",
        out.stdout
    );
}

#[test]
fn calling_through_a_function_kind_param_out_of_its_declared_domain_is_a_real_counterexample() {
    // `f : NatPos -> Int` inside a body that calls `f(x)` for an
    // unconstrained `Int` `x` — a real domain violation (x could be <= 0),
    // must be a genuine counterexample, not a vacuous pass.
    let out = run_file("higher_order_functions_v0_counterexample.cantor");
    assert!(
        out.stdout.contains("counterexample  apply_narrow"),
        "expected a counterexample:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected the domain-violation reason:\n{}",
        out.stdout
    );
}

#[test]
fn call_site_passing_a_mismatched_concrete_function_is_a_real_counterexample() {
    // `weird : NatPos -> Int` passed where `apply` declares `f : (Int ->
    // Int)` — `weird`'s real domain is strictly narrower, so this call
    // genuinely isn't safe (calling weird(-5) inside apply would violate
    // weird's own contract). The structural call-site check must catch
    // this as a real counterexample — not silently accept it (which would
    // make apply's whole body-side proof unearned) and not a crash.
    let out = run_file("higher_order_functions_v0_mismatch.cantor");
    assert!(
        out.stdout.contains("counterexample  main"),
        "expected main to be a counterexample:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected the domain-violation reason:\n{}",
        out.stdout
    );
}

#[test]
fn narrower_range_is_conservatively_rejected_not_a_bug() {
    // `weird_range : Int -> NatPos` — its range is *narrower* than what
    // `apply` declares for `f` (Int), which real covariant-return variance
    // would accept safely (NatPos ⊆ Int). The exact structural Set match
    // this v0 deliberately chose over variance/subtyping (see
    // solver::encode_hof's module doc) rejects it anyway. A real, accepted
    // limitation, not a bug — pinned so a future variance-checking change
    // has a test that must flip from counterexample to proved, not
    // silently regress the other way.
    let out = run_file("higher_order_functions_v0_conservative_reject.cantor");
    assert!(
        out.stdout.contains("counterexample  main"),
        "expected main to be conservatively rejected:\n{}",
        out.stdout
    );
}

#[test]
fn same_kind_bucket_overloaded_name_as_a_value_does_not_crash() {
    // `classify`'s two overloads share Kind Int -> Int, so it's eligible
    // as a value (semantics::elaborate::expr's `Var` arm) and codegen
    // gives it a dispatch-chain wrapper — end-to-end pin that this doesn't
    // crash the CLI.
    let out = run_file("higher_order_functions_v0_overload.cantor");
    assert!(
        !out.stdout.contains("panicked") && !out.stderr.contains("panicked"),
        "must not panic:\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stdout.contains("proved          apply"),
        "expected apply proved:\n{}",
        out.stdout
    );
}

#[test]
fn call_site_passing_an_overloaded_function_is_honestly_unknown_not_falsely_rejected() {
    // `classify` is eligible as a value (one Kind bucket), but its two
    // candidates disagree on their individually *declared* domain Sets
    // (`Nat` vs `Int - Nat` — that's exactly what makes them different
    // overloads), so the call-site structural check can't compare against
    // either one alone without risking a false counterexample (confirmed
    // as a real bug during development: comparing against the first
    // candidate wrongly rejected an actually-safe call). Must stay
    // `unknown` — neither falsely `proved` nor falsely a counterexample.
    let out = run_file("higher_order_functions_v0_overload.cantor");
    assert!(
        out.stdout.contains("unknown         main"),
        "expected main unknown:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("proved          main"),
        "main must not be falsely proved:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("counterexample  main"),
        "main must not be falsely rejected:\n{}",
        out.stdout
    );
}
