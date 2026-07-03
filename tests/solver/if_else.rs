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

// ── Bool / Int branches require explicit conversion ──────────────────────────
// Bool and Int are disjoint in Cantor's value model — `true`/`false` are not
// silently 1/0. A bare `if` with one Int branch and one Bool branch (neither
// a Tuple nor a TaggedUnion) cannot be merged at all; `merge_if_branches`
// rejects it and the whole file fails to elaborate. Converting explicitly
// (`if b then 1 else 0`) makes both branches Int and works normally.

#[test]
fn if_int_then_explicit_bool_conversion_else_proved() {
    // `false` converted explicitly to 0 — both branches are now plain Int.
    proved("
f : Nat -> Int
f(n) = if n > 0 then n else 0
");
}

#[test]
fn if_explicit_bool_conversion_then_int_else_proved() {
    // `true` converted explicitly to 1 — both branches are now plain Int.
    proved("
f : Nat -> Int
f(n) = if n > 0 then 1 else n
");
}

#[test]
fn if_bool_param_then_int_else_explicit_conversion_proved() {
    proved("
f : Bool -> Int
f(b) = if b then 1 else 0
");
}

// Bool/Int mismatch where range catches a violation (the result must still be checked).
#[test]
fn if_int_branches_range_counterexample() {
    // else-branch = 0, but 0 ∉ NatPos → counterexample.
    counterexample("
f : Nat -> NatPos
f(n) = if n > 0 then n else 0
");
}

#[test]
fn if_bare_bool_int_branches_rejected_at_elaboration() {
    // No Tuple/TaggedUnion side and no explicit conversion — merge_if_branches
    // has no coercion for this, so the whole file fails to elaborate rather
    // than silently treating `false` as 0.
    rejected("
f : Nat -> Int
f(n) = if n > 0 then n else false
");
}

// ── Bool branch + fail branch ─────────────────────────────────────────────────
// `Fail` is a builtin distinct sort; `Bool | Fail` is a cross-kind union datatype,
// and both branches are independently coerced into it via `coerce_to`.

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

// ── Tuple branch + fail branch ────────────────────────────────────────────────
// When the range is a cross-kind DT both branches are coerced into the DT
// before the Ite is built; the sort-mismatch fallback is never reached.

#[test]
fn if_tuple_fail_proved() {
    proved("
f : Bool -> (Nat * Nat) | Fail
f(b) = if b then (1, 2) else fail
");
}

// ── Tuple branch in a scalar range — should counterexample ───────────────────
// When the range is a plain scalar set, a tuple branch can never satisfy it.
// The solver should emit a counterexample via the path-conditioned false
// obligation rather than an opaque Unknown.

#[test]
fn if_tuple_branch_in_scalar_range_counterexample() {
    counterexample("
f : Bool -> Nat
f(b) = if b then (1, 2) else 0
");
}

// ── Projection from an if/else result ────────────────────────────────────────
// When both branches are tuples the Ite result has tuple_sort, and
// projecting from it should extract the correct field — not the then-branch.

#[test]
fn if_else_tuple_proj_proved() {
    proved("
f : Bool -> Nat
f(b) = (if b then (1, 2) else (3, 4)).0
");
}

#[test]
fn if_else_tuple_proj_counterexample() {
    // When b is true the tuple is (0, 2); .0 = 0 which is not in NatPos.
    counterexample("
f : Bool -> NatPos
f(b) = (if b then (0, 2) else (3, 4)).0
");
}
