//! `Float32`/`FiniteFloat32` (design-decisions.md §13, "`Float32` /
//! `FiniteFloat32`"). Semantics step DONE: `Float32`/`FiniteFloat32` are
//! registered builtin sets and Kind inference (literals, arithmetic,
//! comparisons, `neg`) works — see tests/semantics/elaborate_tests.rs and
//! tests/kind_tests.rs for that coverage directly. Solver/codegen are not
//! implemented yet, so `solver::mod::reject_float32` (an upstream gate,
//! TODO(float32): delete once those steps land) rejects any program that
//! elaborates a `Kind::Float32` anywhere, cleanly, before the solver or
//! codegen ever run.
//!
//! None of these prove a Float32 program usable yet — that's future work —
//! this is purely "reject cleanly instead of crashing," end to end through
//! the CLI.

use super::helpers::*;

#[test]
fn float32_in_value_position_is_rejected_by_the_upstream_gate() {
    let out = run_file("float32_value_position_not_yet_supported.cantor");
    assert_ne!(
        out.code, 0,
        "expected non-zero exit\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("not yet supported") && out.stderr.contains("Float32"),
        "expected a Float32 'not yet supported' diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
    );
}

#[test]
fn float32_in_signature_domain_is_rejected_by_the_upstream_gate() {
    let out = run_file("float32_domain_position_not_yet_supported.cantor");
    assert_ne!(
        out.code, 0,
        "expected non-zero exit\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("not yet supported") && out.stderr.contains("Float32"),
        "expected a Float32 'not yet supported' diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
    );
}
