//! Regression tests for the "Int64→Int re-tagging gap": a Step-A-promoted
//! function's raw `Kind::Int64` result (int-soundness-plan phase 3,
//! `solver::int64_split`) reaching a position that's always read back out as
//! a *tagged* `Kind::Int` word — a tuple leaf, a fallible function's success
//! payload, or (recursively) an event-loop `main`'s Output tuple — used to
//! be inserted with no re-tagging, silently corrupting the value (or
//! crashing outright, if the raw bit pattern happened to look like a boxed
//! BigInt pointer). Fixed by `Compiler::coerce_int_leaves` (recurses into
//! `Kind::Tuple`, `src/codegen/coerce.rs`), `Compiler::wrap_return_value`
//! (the `{tag, i64}` propagation wire, `src/codegen/mod.rs`), and
//! `Compiler::insert_kind_leaves` (a general `TaggedUnion` arm, same file).
//!
//! `rem_quot.rs`'s fixtures predate this fix and deliberately route around
//! the gap (bare `-> Int` returns only) — see that file's module doc.

use super::helpers::*;

#[test]
fn tuple_leaf_retags_a_promoted_call_result() {
    // -7 quot 5 == -2 (see tests/cli/rem_quot.rs's identical fact) — here
    // returned as the first element of a tuple rather than main's bare
    // return value.
    let out = run_subcommand("int64_retag_tuple_leaf.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = (-2, 100)"),
        "expected the tuple's first leaf to be the correctly-tagged -2:\n{}",
        out.stdout
    );
}

#[test]
fn fail_wire_success_payload_retags_a_promoted_call_result() {
    let out = run_subcommand("int64_retag_fail_wire.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = -2"),
        "expected the fallible success payload to be the correctly-tagged -2:\n{}",
        out.stdout
    );
}
