//! End-to-end CLI behavior for `distinct` over a non-`Int` basis — the
//! generalization of `distinct`'s previously Int-only `mk_D`/`from_D`
//! machinery, see `tests/solver/distinct_basis.rs` for the proof-level
//! coverage of the same generalization across `Bool`/`Char`/`Vector` bases.

use super::helpers::*;

#[test]
fn distinct_tuple_basis_constructor_runs_correctly() {
    let out = run_subcommand("distinct_tuple_basis.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 7"),
        "expected sum_of(point((3, 4))) = 3 + 4 = 7:\n{}",
        out.stdout
    );
}
