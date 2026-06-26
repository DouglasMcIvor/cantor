use super::helpers::*;

// Solver tests for cross-kind union domains and ranges.
// These exercise the Step 6 CVC5 algebraic datatype encoding for unions that
// mix tuple arms with scalar arms — e.g. `(Nat * Nat) | Nat`.

// ── Cross-kind domain ─────────────────────────────────────────────────────────

// Constant body: always 0, so Int range is proved for any cross-kind domain.
#[test]
fn cross_kind_domain_constant_body_proved() {
    proved("
f : (Nat * Nat) | Nat -> Int
f(x) = 0
");
}

// 0 is not in NatPos; should produce a counterexample from the scalar arm.
#[test]
fn cross_kind_domain_constant_body_counterexample() {
    counterexample("
f : (Nat * Nat) | Nat -> NatPos
f(x) = 0
");
}

// ── Cross-kind range ──────────────────────────────────────────────────────────

// Nat is always in `(Nat * Nat) | Nat`'s scalar arm; proved.
#[test]
fn cross_kind_range_scalar_arm_proved() {
    proved("
f : Nat -> (Nat * Nat) | Nat
f(x) = x
");
}

// A negative Int is not in `(Nat * Nat) | Nat`; counterexample.
#[test]
fn cross_kind_range_scalar_arm_negative_counterexample() {
    counterexample("
f : Int -> (Nat * Nat) | Nat
f(x) = x
");
}

// ── Three-arm cross-kind union ────────────────────────────────────────────────

// Constant 0 is always in `Bool | Nat | (Nat * Nat)`.
#[test]
fn three_arm_cross_kind_domain_proved() {
    proved("
f : Bool | Nat | (Nat * Nat) -> Int
f(x) = 0
");
}

// ── If/else coercion (coerce_to hint) ─────────────────────────────────────────

// Both branches coerced to the same DT sort before Ite is built.
#[test]
fn cross_kind_range_if_else_proved() {
    proved("
f : Nat -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, x) else x
");
}

// Tuple arm with a negative component is not in (Nat * Nat).
#[test]
fn cross_kind_range_if_else_tuple_arm_counterexample() {
    counterexample("
f : Nat -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, -1) else x
");
}

// When input can be negative, the scalar arm can be negative too.
#[test]
fn cross_kind_range_if_else_scalar_arm_counterexample() {
    counterexample("
f : Int -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, x) else x
");
}

// Block body with a let-binding before the if/else.
#[test]
fn cross_kind_range_block_if_else_proved() {
    proved("
f : Nat -> (Nat * Nat) | Nat
f(x) {
    y : Nat = x + 1
    if y > 0 then (y, y) else y
}
");
}
