//! JIT-execution proof that calling through a `Kind::Function` value
//! actually runs correctly (indirect call via `inttoptr`/`ptrtoint`,
//! `codegen::expr_call::compile_indirect_call`) — higher-order functions v0,
//! see backlog.md. Uses `compile_file` (unverified — no solver needed),
//! same as this suite's other fixtures; solver-side proof for this shape is
//! a separate, not-yet-landed piece (see `tests/cli/higher_order_functions.rs`).

use super::helpers::jit_src_zero_arg;

#[test]
fn call_through_function_value_executes_correctly() {
    let result = jit_src_zero_arg(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(f, x) = f(x)\n\
         main : -> Int\n\
         main() = apply(double, 5)",
    );
    assert_eq!(result, 10);
}

#[test]
fn call_through_function_value_picks_the_right_function_at_the_call_site() {
    // Two distinct single-signature functions, both taken as values and
    // routed through the same `apply` — confirms the indirect call actually
    // dispatches to whichever function's address was passed, not always the
    // first-declared one.
    let result = jit_src_zero_arg(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         square : Int -> Int\n\
         square(x) = x * x\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(f, x) = f(x)\n\
         main : -> Int\n\
         main() = apply(square, apply(double, 3))",
    );
    // double(3) = 6, square(6) = 36
    assert_eq!(result, 36);
}

#[test]
fn function_value_stored_in_a_local_still_calls_correctly() {
    let result = jit_src_zero_arg(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(f, x) = f(x)\n\
         main : -> Int\n\
         main() {\n\
             mut g : (Int -> Int) = double\n\
             apply(g, 21)\n\
         }",
    );
    assert_eq!(result, 42);
}

// ── Overloaded name as a value (same Kind bucket) ────────────────────────────

#[test]
fn overloaded_name_as_a_value_dispatches_to_the_matching_arm_at_runtime() {
    // `classify`'s two overloads (Nat -> Int, (Int - Nat) -> Int) share Kind
    // Int -> Int, so the name is eligible as a value — codegen must give it
    // a dispatch-chain wrapper (`compile_overload_value_wrappers`) that
    // picks the right arm at runtime, exercised for *both* branches through
    // one indirect call site.
    let result = jit_src_zero_arg(
        "classify : Nat -> Int\n\
         classify(x) = x\n\
         classify : Int - Nat -> Int\n\
         classify(x) = -x\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(f, x) = f(x)\n\
         main : -> Int\n\
         main() = apply(classify, 5) + apply(classify, -5)",
    );
    // classify(5) = 5 (Nat arm), classify(-5) = 5 (negated Int-Nat arm)
    assert_eq!(result, 10);
}
