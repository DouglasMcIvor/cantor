use super::helpers::*;

// ── Same-sort branches (already work, regression guard) ──────────────────────

#[test]
fn if_int_int_proved() {
    proved("
max : Int * Int -> Int
max(a, b) = if a > b then a else b
");
}

#[test]
fn if_bool_bool_proved() {
    proved("
f : Bool -> Bool
f(b) = if b then true else false
");
}

// ── Bool / Int branch unification ────────────────────────────────────────────
// `false` = 0 and `true` = 1 in Cantor's value model (Bool ⊆ Int).
// When one branch encodes to boolean-sort and the other to integer-sort,
// the solver should coerce the boolean to 0/1 rather than erroring.

#[test]
fn if_int_then_bool_else_proved() {
    // false encodes as boolean-sort; n as integer-sort.  After coercion false → 0.
    proved("
f : Nat -> Int
f(n) = if n > 0 then n else false
");
}

#[test]
fn if_bool_then_int_else_proved() {
    // true encodes as boolean-sort; n as integer-sort.  After coercion true → 1.
    proved("
f : Nat -> Int
f(n) = if n > 0 then true else n
");
}

#[test]
fn if_bool_param_then_int_else_bool_proved() {
    proved("
f : Bool -> Int
f(b) = if b then 1 else false
");
}

// Bool/Int mismatch where range catches a violation (the result must still be checked).
#[test]
fn if_bool_int_branches_range_counterexample() {
    // true → 1, n ∈ Nat so n ≥ 0; result is always ≥ 0. But range is NatPos (> 0).
    // When n = 0, result = 1 ∈ NatPos; when n > 0, result = n ∈ NatPos.  Proved!
    // No — let's pick a case that actually counterexamples:
    // f : Nat -> NatPos; f(n) = if n > 0 then n else false
    // else-branch = false → 0, but 0 ∉ NatPos → counterexample
    counterexample("
f : Nat -> NatPos
f(n) = if n > 0 then n else false
");
}

// ── Bool branch + fail branch ─────────────────────────────────────────────────
// `fail` encodes as the integer sentinel i64::MIN.
// `false` and `true` encode as boolean-sort; they should be coerced to 0 and 1.

#[test]
fn if_bool_or_fail_proved() {
    proved("
f : Int -> Bool | Fail
f(n) = if n == 0 then false else fail
");
}

#[test]
fn if_true_or_fail_proved() {
    proved("
f : NatPos -> Bool | Fail
f(n) = if n > 0 then true else fail
");
}

// ── Distinct-sort / Int branch in union range ─────────────────────────────────
// When the range is `D | S` (a cross-kind DT), and one branch is D-sorted
// and the other is integer-sorted, both should be coerced into the DT.

#[test]
fn if_distinct_or_int_branch_proved() {
    proved("
Litre = distinct Nat
f : Bool -> Litre | Nat
f(b) = if b then litre(5) else 3
");
}

#[test]
fn if_distinct_or_int_branch_counterexample() {
    // The Litre arm does not satisfy Nat, so a Litre result fails the range Nat.
    counterexample("
Litre = distinct Nat
f : Bool -> Nat
f(b) = if b then litre(0) else 0
");
}
