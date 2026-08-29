//! End-to-end pin for higher-order functions v0 (backlog.md): `Domain ->
//! Range` as a Kind, and calling through a function-Kind parameter is now
//! genuinely provable/disprovable (not just Kind-checked) inside the
//! *callee's own body* — `apply`'s `f(x)` is checked against `f`'s declared
//! contract from `apply`'s own signature, real counterexamples included.
//!
//! **Still open**, deliberately not covered by a "must be proved" test
//! here: a *caller* passing a concrete function in (`apply(double, 5)`)
//! isn't solver-encodable yet (`Kind::Function` has no CVC5 sort), so that
//! call site reports a clean `unknown` — never a crash, never a false
//! `proved`. See backlog.md's higher-order-functions entry for what's still
//! needed to close that gap.

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
fn calling_through_a_function_kind_param_is_now_provable() {
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
fn call_site_passing_a_concrete_function_is_honestly_unknown_not_a_false_proof() {
    // `main` passes `double` into `apply`'s function-Kind parameter — not
    // solver-encodable yet, so this must be `unknown`, never a silent
    // `proved` (CLAUDE.md's core soundness rule: the compiler never assumes
    // what it hasn't proved).
    let out = run_file("higher_order_functions_v0.cantor");
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
