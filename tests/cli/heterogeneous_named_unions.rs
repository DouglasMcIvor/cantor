//! Named unions whose arms have genuinely different Kinds from each other
//! (`Shape = distinct (Circle: Nat | Rect: Nat * Nat)`) — end-to-end CLI
//! behavior mirroring `tests/cli/named_unions.rs`'s same-Kind-arm case. See
//! `tests/solver/heterogeneous_named_unions.rs` for the proof-level
//! coverage of the same generalization.

use super::helpers::*;

#[test]
fn heterogeneous_named_union_constructors_run_correctly() {
    let out = run_subcommand("heterogeneous_named_union.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3(4, 5)"),
        "expected show(Shape.Circle(3)) ++ show(Shape.Rect((4, 5))) = \"3(4, 5)\":\n{}",
        out.stdout
    );
}

#[test]
fn heterogeneous_named_union_duplicate_kind_arms_run_correctly() {
    // Two labeled arms (`Circle: Nat`, `Square: NatPos`) sharing `Kind::Int`,
    // mixed with a third, differently-Kinded `Rect: Nat * Nat` — used to be
    // rejected by `validate_distinct_basis`'s pairwise-distinctness v0 scope
    // cut; now runs end to end through the real compiled binary (not just
    // the solver-level proof coverage in
    // `tests/solver/heterogeneous_named_unions.rs`).
    let out = run_subcommand("heterogeneous_named_union_duplicate_kind.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3,4,(5, 6)"),
        "expected show(Shape.Circle(3)) ++ \",\" ++ show(Shape.Square(4)) ++ \",\" ++ \
         show(Shape.Rect((5, 6))) = \"3,4,(5, 6)\":\n{}",
        out.stdout
    );
}
