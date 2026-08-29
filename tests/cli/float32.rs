//! `Float32`/`FiniteFloat32` (design-decisions.md §13, "`Float32` /
//! `FiniteFloat32`"), parser slice only — lexer/AST support for `3.14f`,
//! `infinity32`, `nan32` exists, but semantics/solver/codegen do not yet.
//!
//! None of these prove a Float32 program usable yet — that's future work —
//! this is purely "reject cleanly instead of crashing or silently
//! misclassifying the Kind," end to end through the CLI.

use super::helpers::*;

#[test]
fn float32_literal_in_value_position_is_not_yet_supported() {
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
fn float32_literal_in_domain_position_is_not_yet_supported() {
    let out = run_file("float32_domain_position_not_yet_supported.cantor");
    assert_ne!(
        out.code, 0,
        "expected non-zero exit\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("not yet supported")
            && out.stderr.contains("Float32 in set/domain position"),
        "expected a Float32 domain-position diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
    );
}
