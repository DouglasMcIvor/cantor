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
