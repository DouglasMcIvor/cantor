//! Quotient sets (`L / canon`), end to end. See
//! docs/wrapping-and-quotient-sets-plan.md, "Quotient set formation:
//! `L / canonicalizer`".
//!
//! Membership facts are checked via bare `cantor <file>` (proof only, no
//! `run`) rather than `run_subcommand`/`assert`-and-execute: a promoted
//! `Kind::Int64` value flowing into a `Fail`-wire success payload hits a
//! separate, pre-existing display bug unrelated to quotient sets (see
//! `tests/cli/rem_quot.rs`'s module doc) — bare `check` proves the exact
//! same facts without ever touching codegen, so it isn't affected.

use super::helpers::*;

#[test]
fn int_mod5_quotient_set_proves() {
    // The plan's headline example: `IntMod5 = Int / canon5` where
    // `canon5(x) = x rem 5`. Both membership facts are genuinely checked
    // (not vacuously true) — `assert 7 in IntMod5` on its own, in the same
    // file, is confirmed separately to produce a counterexample.
    let out = run_file("quotient_int_mod5_proves.cantor");
    assert_eq!(
        out.code, 0,
        "expected all signatures to prove:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout
            .contains("proved          IntMod5 = Int / canon5 (quotient set)"),
        "expected the quotient-set definition itself to report proved:\n{}",
        out.stdout
    );
}

#[test]
fn non_idempotent_canonicalizer_rejected_with_witness() {
    // `bad_canon(x) = x + 1` is never idempotent (`f(f(x)) = x+2 != x+1 =
    // f(x)` for every x) — a hard compile error per fork 3 of the plan, no
    // `assume` escape hatch.
    let out = run_file("quotient_non_idempotent_rejected.cantor");
    assert_ne!(out.code, 0, "should be rejected:\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  BadQuotient"),
        "expected a counterexample for the quotient definition itself:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not idempotent"),
        "expected an idempotence-failure reason:\n{}",
        out.stdout
    );
}

#[test]
fn non_named_function_canonicalizer_rejected_cleanly() {
    // The RHS of `/` in set position must be a bare named-function
    // reference; `(Int + Int)` isn't one ("lambdas not yet supported" is
    // the forward-looking framing, but any non-Var shape hits this today).
    let out = run_file("quotient_lambda_rejected.cantor");
    assert_ne!(out.code, 0, "should be rejected:\n{}", out.stdout);
    assert!(
        out.stderr
            .contains("canonicalizer must be a named function"),
        "expected the shape diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must be a clean diagnostic, not an ICE:\n{}",
        out.stderr
    );
}

#[test]
fn quotient_value_flows_through_ordinary_int_function_unchanged() {
    // No codegen change for quotient sets at all (docs/wrapping-and-
    // quotient-sets-plan.md: "the actual scope-reducer" — an `IntMod5_32`
    // value is represented identically to a plain `Int`/`Int32` value).
    // `canon5_32(17) = 2`, `double(2) = 4`.
    let out = run_subcommand("quotient_value_through_int_function.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 4"),
        "expected double(canon5_32(17)) == 4:\n{}",
        out.stdout
    );
}
