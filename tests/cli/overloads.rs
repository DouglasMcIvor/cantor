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

/// Guards (`x for x < 0`) are sugar for narrowing one overload arm's
/// already-declared domain by a predicate — see backlog.md's `sign` sketch.
/// `sign(-5) + sign(0) + sign(7)` exercises all three arms: the `{0}`
/// literal-domain arm, and two guarded `Int` arms whose predicates
/// (`x < 0` / `x > 0`) must be proved pairwise disjoint from each other and
/// from `{0}`.
#[test]
fn guarded_overload_arms_dispatch_correctly() {
    let out = run_subcommand("guard_sign.cantor");
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

/// `guarded_overload_arms_dispatch_correctly` above only ever calls `sign`
/// with literal arguments, which the solver can resolve statically — so it
/// never actually exercised codegen's *runtime* dispatch chain for a
/// guarded domain. Routing the call through `helper`'s unconstrained `Int`
/// parameter forces genuine runtime dispatch, which found (and this
/// regression-guards) a real gap: `compile_membership` had no codegen
/// support for a comprehension-shaped domain at all, only the solver side
/// did — see `Compiler::compile_domain_part_match` in overload_dispatch.rs.
#[test]
fn guarded_overload_arms_dispatch_correctly_at_runtime() {
    let out = run_subcommand("guard_runtime_dispatch.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 12"),
        "expected helper(-5) + helper(0) + helper(7) = 5 + 0 + 7 = 12:\n{}",
        out.stdout
    );
}

/// Overlapping guards must be rejected with a disjointness counterexample,
/// same as any other overlapping overload domain.
#[test]
fn overlapping_guard_domains_refuse_to_run_with_witness() {
    let out = run_subcommand("guard_overlap.cantor");
    assert_ne!(
        out.code, 0,
        "overlapping guard domains must refuse to run:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("not disjoint"),
        "expected the witness/reason to explain the overlap:\n{}",
        out.stdout
    );
}

/// Literal-arm overloading (`factorial(0) = 1`) — sugar for narrowing this
/// arm's declared domain to `{0}`, via the same synthesized-guard
/// desugaring path guards use. `factorial`'s own arm keeps a broader
/// declared domain (`Nat`) than its actual proved domain (`{0}`), so this
/// also exercises the narrowing, not just a domain that already happened
/// to be a singleton.
#[test]
fn literal_arm_overload_dispatches_correctly() {
    let out = run_subcommand("literal_arm_factorial.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 120"),
        "expected factorial(5) = 120:\n{}",
        out.stdout
    );
}

#[test]
fn overlapping_literal_arm_domains_refuse_to_run_with_witness() {
    let out = run_subcommand("literal_arm_overlap.cantor");
    assert_ne!(
        out.code, 0,
        "overlapping literal-arm domains must refuse to run:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("not disjoint"),
        "expected the witness/reason to explain the overlap:\n{}",
        out.stdout
    );
}
