use super::helpers::*;

// ── Basic immutable let bindings ──────────────────────────────────────────────

#[test]
fn let_simple_proved() {
    proved("
f : Nat -> Nat
f(n) {
    x : Nat = n + 1
    x
}
");
}

#[test]
fn let_used_in_arithmetic_proved() {
    proved("
double_plus_one : Nat -> Nat
double_plus_one(n) {
    doubled : Nat = n + n
    doubled + 1
}
");
}

#[test]
fn let_constraint_checked_counterexample() {
    counterexample("
bad_let : Nat -> Nat
bad_let(n) {
    x : NatPos = 0
    x
}
");
}

#[test]
fn let_value_not_in_constraint_counterexample() {
    counterexample("
wrong : Int -> Nat
wrong(n) {
    x : Nat = n
    x
}
");
}

#[test]
fn let_multiple_bindings_proved() {
    proved("
triple : Nat -> Nat
triple(n) {
    a : Nat = n
    b : Nat = a + a
    b + n
}
");
}

// ── Immutability enforcement ──────────────────────────────────────────────────

#[test]
fn let_reassign_is_counterexample() {
    counterexample("
mutate_immutable : Nat -> Nat
mutate_immutable(n) {
    x : Nat = n
    x := x + 1
    x
}
");
}

// ── Interaction with mut bindings ─────────────────────────────────────────────

#[test]
fn let_and_mut_coexist_proved() {
    proved("
mixed : Nat -> Nat
mixed(n) {
    base : Nat = 10
    mut acc : Nat = base
    mut i : Nat = 0
    while i < n {
        acc := acc + base
        i := i + 1
    }
    acc
}
");
}

#[test]
fn let_used_as_loop_limit_proved() {
    proved("
sum_to_limit : Nat -> Nat
sum_to_limit(n) {
    limit : Nat = n
    mut acc : Nat = 0
    mut i : Nat = 0
    while i <= limit {
        acc := acc + i
        i := i + 1
    }
    acc
}
");
}

// ── Constraint narrows the solver's view of the value ─────────────────────────

#[test]
fn let_constraint_enables_downstream_proof() {
    proved("
sum_positive : Nat -> NatPos
sum_positive(n) {
    one : NatPos = 1
    n + one
}
");
}
