use super::helpers::*;

// Solver tests for cross-kind union domains and ranges.
// These exercise the Step 6 CVC5 algebraic datatype encoding for unions that
// mix tuple arms with scalar arms — e.g. `(Nat * Nat) | Nat`.

// ── Cross-kind domain ─────────────────────────────────────────────────────────

// Constant body: always 0, so Int range is proved for any cross-kind domain.
#[test]
fn cross_kind_domain_constant_body_proved() {
    proved(
        "
f : (Nat * Nat) | Nat -> Int
f(x) = 0
",
    );
}

// 0 is not in NatPos; should produce a counterexample from the scalar arm.
#[test]
fn cross_kind_domain_constant_body_counterexample() {
    counterexample(
        "
f : (Nat * Nat) | Nat -> NatPos
f(x) = 0
",
    );
}

// ── Cross-kind range ──────────────────────────────────────────────────────────

// Nat is always in `(Nat * Nat) | Nat`'s scalar arm; proved.
#[test]
fn cross_kind_range_scalar_arm_proved() {
    proved(
        "
f : Nat -> (Nat * Nat) | Nat
f(x) = x
",
    );
}

// A negative Int is not in `(Nat * Nat) | Nat`; counterexample.
#[test]
fn cross_kind_range_scalar_arm_negative_counterexample() {
    counterexample(
        "
f : Int -> (Nat * Nat) | Nat
f(x) = x
",
    );
}

// ── Three-arm cross-kind union ────────────────────────────────────────────────

// Constant 0 is always in `Bool | Nat | (Nat * Nat)`.
#[test]
fn three_arm_cross_kind_domain_proved() {
    proved(
        "
f : Bool | Nat | (Nat * Nat) -> Int
f(x) = 0
",
    );
}

// ── If/else coercion (coerce_to hint) ─────────────────────────────────────────

// Both branches coerced to the same DT sort before Ite is built.
#[test]
fn cross_kind_range_if_else_proved() {
    proved(
        "
f : Nat -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, x) else x
",
    );
}

// Tuple arm with a negative component is not in (Nat * Nat).
#[test]
fn cross_kind_range_if_else_tuple_arm_counterexample() {
    counterexample(
        "
f : Nat -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, -1) else x
",
    );
}

// When input can be negative, the scalar arm can be negative too.
#[test]
fn cross_kind_range_if_else_scalar_arm_counterexample() {
    counterexample(
        "
f : Int -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, x) else x
",
    );
}

// ── Projection from a cross-kind union parameter ─────────────────────────────
// When a parameter has a cross-kind union domain its term has DT sort.
// Projecting a field should:
//   • push a tester obligation (the value must be in the tuple arm) so the
//     solver finds a counterexample if the scalar arm is reachable, and
//   • use an ApplySelector on the DT to extract the field.

// If x is always the tuple (Nat * Nat) arm, x.0 is always in Nat — proved.
#[test]
fn cross_kind_domain_proj_proved() {
    proved(
        "
f : (Nat * Nat) -> Nat
f(x) = x.0
",
    );
}

// x is from (Nat * Nat) | Nat.  The scalar arm has no .0; should counterexample.
#[test]
fn cross_kind_domain_proj_scalar_arm_counterexample() {
    counterexample(
        "
f : (Nat * Nat) | Nat -> Nat
f(x) = x.0
",
    );
}

// Block body with a let-binding before the if/else.
#[test]
fn cross_kind_range_block_if_else_proved() {
    proved(
        "
f : Nat -> (Nat * Nat) | Nat
f(x) {
    y : Nat = x + 1
    if y > 0 then (y, y) else y
}
",
    );
}

// Regression test: two union arms with the *identical* tuple shape are
// same-Kind (`kind::union_if_distinct` dedups them to a bare `Kind::Tuple`,
// no tag), so `.0`/`.1` projection must resolve directly, not treat the
// domain as a genuine cross-kind datatype with no matching arm. Before
// `solver::sort::set_sort`'s union arm checked `ls == rs` for tuple/DT
// sorts (only the sequence/Bool cases checked this), this fell through the
// "no matching tuple arm" fallback and came back a fabricated
// counterexample for a provably-valid program. Found while generalizing
// `distinct`'s basis beyond `Int` — see backlog.md.
#[test]
fn identical_shape_tuple_union_domain_projection_proved() {
    proved(
        "
f : (Nat * Nat) | (Nat * Nat) -> Nat
f(p) = p.0 + p.1
",
    );
}
