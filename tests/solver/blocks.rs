use super::helpers::*;

// ── `return` statements ───────────────────────────────────────────────────────
//
// `return expr` exits the function immediately, exactly like codegen's
// `compile_return_stmt` (a real `ret`, with unreachable code after it). The
// current grammar has no statement-level branching in a flat block (`if` is
// value-position only; `while`/`for` bodies go through a separate induction
// path, never this encoder), so a `return` reached here is unconditionally
// reached — encoding it and exiting right away is sound, not an approximation.

#[test]
fn return_simple_proved() {
    proved("
f : Nat -> Nat
f(n) {
    return n + 1
}
");
}

#[test]
fn return_after_let_proved() {
    proved("
f : Nat -> Nat
f(n) {
    x : Nat = n + 1
    return x + 1
}
");
}

#[test]
fn return_value_outside_range_counterexample() {
    counterexample("
f : Nat -> NatPos
f(n) {
    return n
}
");
}

// Anything after `return` is unreachable dead code — the solver must not
// consider it at all, even when it would itself be unsafe if it ever ran.
// `n - 100` is negative (not in Nat) for n < 100, but since it's dead code
// after the first `return`, the function is still fully proved.
#[test]
fn return_dead_code_after_return_is_never_checked_proved() {
    proved("
f : Nat -> Nat
f(n) {
    return n + 1
    return n - 100
}
");
}

// A `return` in the tail position of a nested `{ }` scope block (itself in
// tail position of the outer block) is handled by `encode_block`'s existing
// `SemStmt::Block` recursion.
#[test]
fn return_in_tail_position_of_nested_block_proved() {
    proved("
f : Nat -> Nat
f(n) {
    {
        x : Nat = n + 1
        return x
    }
}
");
}

// ── `return` inside a loop body — must never be silently ignored ────────────
//
// `while`/`for` bodies are never processed by `encode_block`'s own statement
// loop (they go through the separate induction-based reasoning in
// `loops.rs`), so a naive `return`-anywhere fix would make the early-exit
// value invisible to the checked function result — silently proving
// properties about whatever comes *after* the loop, even though the function
// may never reach that code at runtime. This must report Unknown, not a
// false Proved. (Regression test for exactly that soundness bug, caught
// during review before this fix was landed.)

#[test]
fn return_inside_while_body_is_unknown_not_falsely_proved() {
    // If this reported Proved, it would be unsound: x < 1 is true at n = 0,
    // so the loop body runs once and the function actually returns 0 at
    // runtime — not in NatPos — regardless of what the code after the loop
    // says.
    unknown("
f : Nat -> NatPos
f(n) {
    x : Nat = 0
    while x < 1 {
        x := x + 1
        return 0
    }
    return 1
}
");
}

#[test]
fn return_inside_for_body_is_unknown_not_falsely_proved() {
    unknown("
f : Nat -> NatPos
f(n) {
    for x in {0, 1} {
        return 0
    }
    return 1
}
");
}

// A `for` loop over a provably-empty set literal never runs its body at all,
// so a `return` inside it is genuinely unreachable dead code — this should
// still prove, not conservatively report Unknown.
#[test]
fn return_inside_empty_for_body_is_dead_code_proved() {
    proved("
f : Nat -> Nat
f(n) {
    for x in {} {
        return 999
    }
    return n
}
");
}
