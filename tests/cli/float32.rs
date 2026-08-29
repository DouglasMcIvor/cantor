//! `Float32`/`FiniteFloat32` (design-decisions.md §13, "`Float32` /
//! `FiniteFloat32`") — all three steps DONE (parser, semantics, solver,
//! codegen). `cantor <file>` proves signatures; `cantor run` actually
//! compiles and executes them. See tests/semantics/elaborate_tests.rs and
//! tests/kind_tests.rs for Kind-inference coverage, and
//! tests/solver/float32.rs for the proof-level coverage of the same
//! equality/comparison claims this file confirms at runtime.

use super::helpers::*;

#[test]
fn float32_check_only_mode_proves_the_signature() {
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
fn float32_run_prints_literal() {
    let out = run_subcommand("float32_value_position.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3.14f"),
        "expected 'main() = 3.14f' in output:\n{}",
        out.stdout
    );
}

#[test]
fn float32_run_arithmetic() {
    // -(1.0f) + 2.0f * 3.0f - 4.0f / 2.0f = -1 + 6 - 2 = 3
    let out = run_subcommand("float32_arith.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3f"),
        "expected 'main() = 3f' in output:\n{}",
        out.stdout
    );
}

#[test]
fn float32_run_equality_and_comparison_match_what_the_solver_proved() {
    // Runtime confirmation that codegen's `==`/`<` agree with the exact
    // same SMT-LIB FP semantics tests/solver/float32.rs proves symbolically
    // — the soundness-critical property that motivated codegen's `==`
    // (bit-pattern-equal OR both-NaN, not a plain `fcmp oeq`).
    let out = run_subcommand("float32_equality_runtime.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected 'main() = 1' (true) in output:\n{}",
        out.stdout
    );
}

#[test]
fn float32_run_show_and_interpolation() {
    let out = run_subcommand("float32_show.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains(
            "pi~3.14f, inf~infinity32, ninf~-infinity32, nan~nan32, \
             zero~0f, negzero~-0f"
        ),
        "expected all six Float32 values shown correctly:\n{}",
        out.stdout
    );
}
