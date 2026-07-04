//! int-soundness-plan phase 2: function overloading with multiple bodies —
//! LLVM IR shape assertions (execution-level behavior is covered end-to-end
//! by tests/cli/overloads.rs; these confirm *how* codegen got there).

use super::helpers::*;

#[test]
fn non_overloaded_function_keeps_its_plain_name() {
    // Regression guard: a name with exactly one `FunctionDef` must compile
    // identically to before phase 2 — no mangling, no dispatch machinery.
    let ir =
        ir_for_src("double : Int -> Int\ndouble(x) = x + x\nmain : -> Int\nmain() = double(5)");
    assert!(
        ir.contains("@double("),
        "expected the plain function name in the IR:\n{ir}"
    );
    assert!(
        !ir.contains("__ov"),
        "non-overloaded functions must not be mangled:\n{ir}"
    );
    assert!(
        !ir.contains("ov_trap"),
        "non-overloaded calls must not emit dispatch-chain machinery:\n{ir}"
    );
}

#[test]
fn overloaded_functions_are_mangled_by_index() {
    let ir = ir_for_src(
        "classify : Nat -> Int\n\
         classify(x) = x\n\
         classify : Int - Nat -> Int\n\
         classify(x) = -x\n\
         main : -> Int\n\
         main() = classify(5)",
    );
    assert!(
        ir.contains("@classify__ov0("),
        "expected the first overload mangled by index 0:\n{ir}"
    );
    assert!(
        ir.contains("@classify__ov1("),
        "expected the second overload mangled by index 1:\n{ir}"
    );
    assert!(
        !ir.contains("@classify("),
        "the bare overloaded name must never be used as an LLVM function name:\n{ir}"
    );
}

#[test]
fn unresolvable_call_emits_a_runtime_dispatch_chain() {
    // `llvm-ir`'s `compile_to_ir` skips the solver entirely, so it always
    // shows the dispatch chain (mirrors the existing `overflow_checks`
    // precedent — proved/elided vs unproved/checked can't be distinguished
    // here either); this asserts the chain's shape, not which branch a
    // *verified* build would pick (that's `tests/solver/overloads.rs` and
    // the `cantor run`-level tests in `tests/cli/overloads.rs`).
    let ir = ir_for_src(
        "classify : Nat -> Int\n\
         classify(x) = x\n\
         classify : Int - Nat -> Int\n\
         classify(x) = -x\n\
         main : Int -> Int\n\
         main(x) = classify(x)",
    );
    assert!(
        ir.contains("ov_call"),
        "expected per-candidate call blocks in the dispatch chain:\n{ir}"
    );
    assert!(
        ir.contains("ov_merge"),
        "expected a phi merge block combining every candidate's result:\n{ir}"
    );
    assert!(
        ir.contains("ov_trap"),
        "expected a trap block for the (proof-only) unreachable else-arm:\n{ir}"
    );
    assert!(
        ir.contains("cantor_dispatch_unreachable"),
        "expected a call to the loud runtime trap, not a silent `unreachable`:\n{ir}"
    );
}

#[test]
fn arity_uniquely_resolved_overload_compiles_to_a_direct_call() {
    // Two overloads of different arity: a 1-arg call has exactly one
    // arity-matching candidate, so it's a direct call — no membership test,
    // no dispatch chain — even though `compile_to_ir` never ran the solver.
    let ir = ir_for_src(
        "poly : Int -> Int\n\
         poly(x) = x\n\
         poly : Int * Int -> Int\n\
         poly(x, y) = x + y\n\
         main : -> Int\n\
         main() = poly(5)",
    );
    assert!(
        ir.contains("@poly__ov0("),
        "expected a direct call to the 1-arg overload:\n{ir}"
    );
    assert!(
        !ir.contains("ov_trap"),
        "arity alone should resolve this call with no dispatch chain:\n{ir}"
    );
}

#[test]
fn runtime_dispatch_picks_the_correct_branch_for_each_input() {
    // Belt-and-braces execution check at the codegen layer (JIT-evaluated
    // directly, bypassing the CLI) that the dispatch chain built above
    // actually computes the right answer on both sides of the domain split.
    let src = "classify : Nat -> Int\n\
               classify(x) = x\n\
               classify : Int - Nat -> Int\n\
               classify(x) = -x\n\
               main : Int -> Int\n\
               main(x) = classify(x)";
    assert_eq!(jit_src_one_arg(src, 7), 7);
    assert_eq!(jit_src_one_arg(src, -4), 4);
}
