//! End-to-end pin for higher-order functions v0 (backlog.md): `Domain ->
//! Range` as a Kind parses and elaborates cleanly all the way through
//! `cantor check`, and — since call-site domain-obligation proof through a
//! function-Kind parameter is deliberately not implemented yet (solver
//! step) — the compiler reports a clean `unknown` rather than crashing or
//! (worse) a false `proved`. This is the CLAUDE.md-required end-to-end test
//! for the parser+semantics half of the feature landed so far.

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
fn call_through_function_value_is_honestly_unknown_not_a_false_proof() {
    // No solver support yet for a call routed through a function-Kind
    // parameter (`f(x)` inside `apply`) — must be `unknown`, never a silent
    // `proved` (CLAUDE.md's core soundness rule: the compiler never assumes
    // what it hasn't proved).
    let out = run_file("higher_order_functions_v0.cantor");
    assert!(
        out.stdout.contains("unknown         apply"),
        "expected apply unknown:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("proved          apply"),
        "apply must not be falsely proved:\n{}",
        out.stdout
    );
}
