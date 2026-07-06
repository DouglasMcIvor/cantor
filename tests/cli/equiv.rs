//! `equiv f, g` — function equivalence checking. A top-level declaration
//! asserting two functions agree on their shared domain, checked by
//! encoding both bodies over one shared symbolic input and asking cvc5 to
//! refute "these disagree somewhere" — the same proved/counterexample/
//! unknown story as ordinary domain/range checking, applied to a new kind
//! of claim. Purely a compile-time proof obligation (like `require`); it
//! introduces no runtime value, no `Kind`, no codegen at all.
//!
//! v0 scope, mirroring the same restriction quotient-set canonicalizers
//! already have (docs/wrapping-and-quotient-sets-plan.md): single-parameter,
//! single-expression-body functions only (reuses `encode_comp_expr`, which
//! doesn't support calls/if-else/block bodies). Extending to richer bodies
//! is a natural follow-up using the full `encode_expr`/`EncodeCtx` machinery
//! instead.

use super::helpers::*;

#[test]
fn equivalent_functions_proved() {
    // x + x and 2 * x really do agree on every Int.
    let out = run_file("equiv_proved.cantor");
    assert_eq!(
        out.code, 0,
        "expected success:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("proved          equiv double1, double2"),
        "expected the equiv declaration itself to report proved:\n{}",
        out.stdout
    );
}

#[test]
fn non_equivalent_functions_get_counterexample() {
    // inc(x) = x + 1 vs inc_wrong(x) = x + 2 disagree everywhere.
    let out = run_file("equiv_counterexample.cantor");
    assert_ne!(out.code, 0, "should be rejected:\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  equiv inc, inc_wrong"),
        "expected a counterexample for the equiv declaration itself:\n{}",
        out.stdout
    );
}

#[test]
fn equiv_quantifies_over_shared_domain_not_full_int() {
    // p/q disagree everywhere but their declared domains (Nat, NegInt) are
    // disjoint -- claim is vacuously true over the (empty) shared domain.
    let out = run_file("equiv_restricted_domain.cantor");
    assert_eq!(
        out.code, 0,
        "expected success (vacuously true over an empty shared domain):\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("proved          equiv p, q"),
        "expected the equiv declaration to report proved:\n{}",
        out.stdout
    );
}

#[test]
fn equiv_referencing_undefined_function_reports_unknown_not_ice() {
    let out = run_file("equiv_undefined_function.cantor");
    assert_ne!(out.code, 0, "should not succeed:\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("unknown         equiv f, g"),
        "expected an unknown result for the equiv declaration itself:\n{}",
        out.stdout
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
    );
}
