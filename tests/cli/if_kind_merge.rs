//! End-to-end coverage for `kind::merge_if_branches`'s `AppendThenArm`/
//! `AppendElseArm` cases — a chained `if`/`else if`/`else` whose branches
//! revisit a Kind already present in an inner branch's TaggedUnion. See
//! `tests/semantics/elaborate_tests.rs::if_extends_tagged_union_with_arm_matching_an_existing_kind`
//! for the Kind-level assertion; this file confirms the fix all the way
//! through codegen and `show()`.

use super::helpers::*;

#[test]
fn if_chain_duplicate_kind_arm_runs_correctly() {
    let out = run_subcommand("if_chain_duplicate_kind_arm.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5|6|(3, 4)"),
        "expected show(f(true,false)) ++ \"|\" ++ show(f(false,true)) ++ \"|\" ++ \
         show(f(false,false)) = \"5|6|(3, 4)\":\n{}",
        out.stdout
    );
}
