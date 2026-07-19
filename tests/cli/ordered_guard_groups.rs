//! Ordered guard groups: a signature followed directly by 2+ bodies with no
//! repeated signature line between them — end-to-end CLI behavior (ordered
//! static/runtime dispatch, coverage-gap rejection, bare-param rejection,
//! mixing rejection). Mirrors `tests/cli/overloads.rs`'s structure for the
//! pre-existing, always-disjoint overload form.

use super::helpers::*;

#[test]
fn ordered_guard_group_dispatches_correctly() {
    let out = run_subcommand("ordered_guard_sign.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 12"),
        "expected sign(-5) + sign(0) + sign(7) = 5 + 0 + 7 = 12:\n{}",
        out.stdout
    );
}

/// `classify`'s arms deliberately overlap (`x >= 0` and `x > 5` both match
/// `x = 10`) — legal only because an ordered guard group resolves ambiguity
/// by declaration order. Routed through `helper`'s unconstrained `Int`
/// parameter to force genuine runtime dispatch, not just static resolution,
/// so this proves first-match-wins survives end to end through the LLVM
/// dispatch chain.
#[test]
fn ordered_guard_group_runtime_dispatch_respects_declaration_order() {
    let out = run_subcommand("ordered_guard_runtime_dispatch.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected helper(10) + helper(-3) + helper(3) = 1 + 3 + 1 = 5 \
         (helper(10) must hit the first-declared `x >= 0` arm, not the \
         also-matching `x > 5` arm):\n{}",
        out.stdout
    );
}

#[test]
fn ordered_guard_group_coverage_gap_refuses_to_run_with_witness() {
    let out = run_subcommand("ordered_guard_coverage_gap.cantor");
    assert_ne!(
        out.code, 0,
        "a provable coverage gap must refuse to run:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("counterexample") && out.stdout.contains("ordered guard group"),
        "expected a coverage counterexample naming the ordered guard group:\n{}",
        out.stdout
    );
}

#[test]
fn bare_unguarded_param_in_ordered_group_refuses_to_compile() {
    let out = run_subcommand("ordered_guard_bare_param_rejected.cantor");
    assert_ne!(
        out.code, 0,
        "a bare unguarded param inside an ordered guard group must refuse to compile:\n\
         stdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("bare") || out.stderr.contains("bare"),
        "expected the error to explain the bare-param problem:\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}

#[test]
fn ordered_group_mixed_with_hand_disjoint_overload_refuses_to_compile() {
    let out = run_subcommand("ordered_guard_mixed_with_disjoint_rejected.cantor");
    assert_ne!(
        out.code, 0,
        "an ordered guard group mixed with a hand-written disjoint overload of the same \
         (name, arity, kind) must refuse to compile:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
}
