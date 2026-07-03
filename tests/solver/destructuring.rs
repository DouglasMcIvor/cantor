use super::helpers::*;

// ── DestructLet: basic immutable destructuring ────────────────────────────────

#[test]
fn destruct_let_no_constraints_proved() {
    proved("
f : Int * Int -> Int
f(p) {
    x, y = (p.0, p.1)
    x + y
}
");
}

#[test]
fn destruct_let_nat_constraints_proved() {
    proved("
f : Nat * Nat -> Nat
f(p) {
    x : Nat, y : Nat = (p.0, p.1)
    x + y
}
");
}

#[test]
fn destruct_let_literal_proved() {
    proved("
f : -> Int
f() {
    x, y = (-3, 4)
    x + y
}
");
}

// ── DestructLet: constraint violations ───────────────────────────────────────

#[test]
fn destruct_let_bad_constraint_counterexample() {
    counterexample("
f : Int -> Int
f(n) {
    x : NatPos, y : Int = (n, 0)
    x + y
}
");
}

#[test]
fn destruct_let_immutable_reassign_counterexample() {
    counterexample("
f : Int -> Int
f(n) {
    x, y = (n, n + 1)
    x := y
    x
}
");
}

// ── DestructMutLet: mutable destructuring ────────────────────────────────────

#[test]
fn destruct_mut_let_proved() {
    proved("
f : Int * Int -> Int
f(p) {
    mut a : Int, b : Int = (p.0, p.1)
    a := b
    a + p.0
}
");
}

#[test]
fn destruct_mut_nat_constraint_proved() {
    proved("
f : Nat * Nat -> Nat
f(p) {
    mut a : Nat, b : Nat = (p.0, p.1)
    a := a + 1
    a + b
}
");
}

// ── Partial destructuring: last binder collects tail ─────────────────────────

#[test]
fn partial_destruct_proved() {
    proved("
f : Int * Int * Int -> Int
f(p) {
    a, rest = (p.0, p.1, p.2)
    a + rest.0 + rest.1
}
");
}

#[test]
fn partial_destruct_nat_constraint_proved() {
    proved("
f : Nat * Nat * Nat -> Nat
f(p) {
    a : Nat, rest : Nat * Nat = (p.0, p.1, p.2)
    a + rest.0 + rest.1
}
");
}

#[test]
fn partial_destruct_bad_head_counterexample() {
    counterexample("
f : Int -> Int
f(n) {
    a : NatPos, rest = (n, 0, 0)
    a + rest.0
}
");
}

// ── DestructAssign: reassignment of existing mutables ────────────────────────

#[test]
fn destruct_assign_swap_proved() {
    proved("
f : Int * Int -> Int
f(p) {
    mut a : Int, b : Int = (p.0, p.1)
    a, b := (p.1, p.0)
    a + b
}
");
}

#[test]
fn destruct_assign_nat_constraint_violation_counterexample() {
    counterexample("
f : Nat * Nat -> Nat
f(p) {
    mut a : Nat, b : Nat = (p.0, p.1)
    a, b := (b - 1, a)
    a + b
}
");
}

// ── Non-integer components ────────────────────────────────────────────────────
//
// Destructure SSA constants take each projection's own sort; Bool components
// used to be bound to integer-sorted constants, aborting cvc5.

#[test]
fn destruct_let_bool_components_proved() {
    proved("
f : Bool * Bool -> Bool
f(p) {
    x, y = (p.0, p.1)
    x and y
}
");
}

// ── Vector destructuring: not yet implemented ────────────────────────────────
//
// The README documents `h, t = v` for a vector `v` (head elements plus a
// vector tail, proof-gated on `v` having enough elements) — none of
// elaborate/solver/codegen support this yet. Both statement forms must
// report it clearly (a "not yet implemented" `CompileError`/`Unknown`) —
// never a raw cvc5 abort or a misleading generic "wrong shape" message.

#[test]
fn destruct_let_vector_rhs_rejected() {
    rejected("
f : Nat* -> Nat
f(xs) {
    h, t = xs
    h
}
");
}

#[test]
fn vector_param_destructure_rejected() {
    // The README documents `foo(x, y)` on a `Nat* - {[]}` domain (proof-gated
    // non-empty vector) as binding `x` to the head and `y` to the tail — this
    // reuses the same tuple-arity-disambiguation path as `f(x, y)` on an
    // `Int * Int` domain, and isn't implemented for a vector domain.
    rejected("
foo : (Nat* - {[]}) -> Nat
foo(x, y) = x
");
}

#[test]
fn destruct_assign_vector_rhs_unknown() {
    // `:=` isn't gated at elaboration time (it reuses existing mutable
    // bindings' Kind rather than computing new ones), so this is caught in
    // the solver instead — previously a raw `cvc5: error: index out of
    // bound` abort (the vector RHS is an opaque integer term with no
    // children, and the destructuring code unconditionally called `child()`).
    unknown("
f : Nat* -> Nat
f(xs) {
    mut h : Nat = 0
    mut t : Nat* = []
    h, t := xs
    h
}
");
}
