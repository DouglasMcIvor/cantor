//! int-soundness-plan phase 2: function overloading with multiple bodies —
//! end-to-end CLI behavior (static dispatch, runtime dispatch, overlap
//! rejection, recursion across overloads).

use super::helpers::*;

#[test]
fn statically_resolved_overload_call_runs_correctly() {
    // `classify(5)`: 5 is a literal the solver can place in `Nat` directly,
    // so this resolves to a direct call at compile time — no dispatch chain.
    let out = run_subcommand("overload_static.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected classify(5) via the Nat overload:\n{}",
        out.stdout
    );
}

#[test]
fn unresolved_overload_call_dispatches_correctly_at_runtime() {
    // `helper`'s own parameter is unconstrained `Int`, so `classify(x)`
    // inside its body can't be resolved statically — both `helper(7)` (Nat
    // branch) and `helper(-4)` (Int-Nat branch) must go through the runtime
    // membership-test dispatch chain and pick the right one.
    let out = run_subcommand("overload_runtime_dispatch.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 11"),
        "expected helper(7) + helper(-4) = 7 + 4 = 11:\n{}",
        out.stdout
    );
}

#[test]
fn overlapping_overload_domains_refuse_to_run_with_witness() {
    let out = run_subcommand("overload_overlap.cantor");
    assert_ne!(
        out.code, 0,
        "overlapping overload domains must refuse to run:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("counterexample  over (overload"),
        "expected a disjointness counterexample in the report:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not disjoint"),
        "expected the witness/reason to explain the overlap:\n{}",
        out.stdout
    );
}

/// backlog.md's top item: `f : Bool -> Bool` and `f : Nat -> Nat` coexist as
/// one overload set even though they disagree on Kind (see
/// `tests/semantics/elaborate_tests.rs::overloads_with_different_kinds_are_allowed`
/// and the sibling tests in `tests/solver/overloads.rs` and
/// `tests/codegen/overloads.rs` for the specific layers involved).
#[test]
fn overloads_spanning_different_kinds_run_correctly() {
    let out = run_subcommand("overload_different_kinds.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3"),
        "expected f(3) via the Nat overload:\n{}",
        out.stdout
    );
}

#[test]
fn recursion_where_one_overload_calls_another_runs_correctly() {
    // `count_down`'s NatPos overload recurses into itself and eventually the
    // `{0}` overload — each recursive call site's resolution genuinely
    // varies per call (can't statically prove which arm `x - 1` lands in),
    // so this also exercises the runtime dispatch chain repeatedly.
    let out = run_subcommand("overload_recursion.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected count_down(5) = 5:\n{}",
        out.stdout
    );
}
