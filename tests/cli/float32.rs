//! `Float32`/`FiniteFloat32` (design-decisions.md §13, "`Float32` /
//! `FiniteFloat32`"). Semantics and solver steps DONE: `cantor <file>`
//! (bare check-only mode, no codegen) elaborates and *proves* Float32
//! signatures for real — see tests/semantics/elaborate_tests.rs and
//! tests/solver/float32.rs for that coverage directly. Codegen isn't
//! implemented yet, so `cantor run`/`cantor build` — which both compile —
//! are rejected cleanly by `main::reject_float32_before_codegen` (an
//! upstream gate, TODO(float32): delete once the codegen step lands)
//! instead of crashing trying to compile a `Kind::Float32` value.

use super::helpers::*;

#[test]
fn float32_check_only_mode_proves_the_signature() {
    // Bare `cantor <file>` never reaches codegen at all — proof-only.
    let out = run_file("float32_value_position.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("1 proved"),
        "expected '1 proved' in summary:\n{}",
        out.stdout
    );
}

#[test]
fn float32_in_signature_domain_check_only_mode_proves() {
    let out = run_file("float32_domain_position.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("1 proved"),
        "expected '1 proved' in summary:\n{}",
        out.stdout
    );
}

#[test]
fn float32_in_value_position_is_rejected_before_run_codegen() {
    let out = run_subcommand("float32_value_position.cantor");
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
fn float32_in_signature_domain_is_rejected_before_run_codegen() {
    let out = run_subcommand("float32_domain_position.cantor");
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
