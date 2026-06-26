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
