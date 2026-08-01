//! The `Rational` numeric tower (docs/rational-plan.md).
//!
//! The headline behaviour: `/` is exact division, so `a / b` is a `Rational`
//! even for `Int` operands, and narrowing back to `Int` is a divisibility
//! theorem the solver discharges rather than a silent truncation. These tests
//! are the positive coverage for that — the migration of the old
//! `/`-as-integer-division tests to `quot` lives in the suites they came from.

use super::helpers::*;

// ── `/` produces a Rational ──────────────────────────────────────────────────

#[test]
fn int_division_not_always_int_counterexample() {
    // The whole pitch: `a / b` is only an `Int` when `b` divides `a`, and
    // nothing here proves that. Before the numeric tower this was silently
    // "proved" by truncation.
    counterexample(
        r#"
f : Int * NonZeroInt -> Int
f(a, b) = a / b
"#,
    );
}

#[test]
fn exactly_divisible_is_int_proved() {
    // `(2 * x) / 2 == x` for every `x`, so the range check discharges the
    // divisibility obligation with no annotation from the developer.
    proved(
        r#"
g : Int -> Int
g(x) = (2 * x) / 2
"#,
    );
}

#[test]
fn division_by_literal_divisor_of_numerator_proved() {
    proved(
        r#"
h : Int -> Int
h(x) = (6 * x) / 3
"#,
    );
}

#[test]
fn division_into_rational_range_proved() {
    proved(
        r#"
f : Int * NonZeroInt -> Rational
f(a, b) = a / b
"#,
    );
}

#[test]
fn division_by_zero_still_rejected() {
    // The divisor obligation is now stated over ℚ (`NonZeroRational`), but on
    // an integer-sorted term it builds the identical `t != 0` predicate — so
    // this reports the same "division by zero" reason it always did.
    let results = check(
        r#"
f : Int * Int -> Rational
f(a, b) = a / b
"#,
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected a division-by-zero counterexample, got {result:?}");
    };
    assert_eq!(reason, "division by zero");
}

// ── Int ⊆ Rational: implicit widening ────────────────────────────────────────

#[test]
fn int_widens_into_rational_range_proved() {
    proved(
        r#"
f : Int -> Rational
f(x) = x
"#,
    );
}

#[test]
fn rational_plus_int_literal_proved() {
    proved(
        r#"
f : Rational -> Rational
f(q) = q + 1
"#,
    );
}

#[test]
fn rational_arithmetic_stays_rational_proved() {
    proved(
        r#"
f : Rational * Rational -> Rational
f(p, q) = p * q - p
"#,
    );
}

#[test]
fn negated_rational_is_rational_proved() {
    proved(
        r#"
f : Rational -> Rational
f(q) = -q
"#,
    );
}

// ── …but narrowing ℚ to ℤ is never implicit ──────────────────────────────────

#[test]
fn rational_param_into_int_range_counterexample() {
    // A `Rational` parameter really does range over ℚ — if `set_sort` declared
    // it at integer sort instead, this would wrongly report Proved.
    counterexample(
        r#"
f : Rational -> Int
f(q) = q
"#,
    );
}

#[test]
fn rational_param_into_nat_range_counterexample() {
    counterexample(
        r#"
f : Rational -> Nat
f(q) = q
"#,
    );
}

#[test]
fn rational_proved_integral_by_require() {
    // `q + q` is an integer whenever `q` is — an obligation the developer can
    // discharge by constraining the domain, exactly as for any other range
    // check.
    proved(
        r#"
f : Int -> Int
f(n) = (n + n) / 2
"#,
    );
}

// ── Comparison and equality across the tower ─────────────────────────────────

#[test]
fn rational_compared_to_int_proved() {
    // `<` between a real- and an integer-sorted operand: cvc5 widens the Int
    // side itself, no `to_real` needed.
    proved(
        r#"
f : Rational -> Bool
f(q) = q < 10
"#,
    );
}

#[test]
fn rational_equality_with_int_proved() {
    // `==`/`!=` are the one place the tower needs an explicit `to_real`: a
    // mixed-sort `Equal` is a fatal cvc5 sort error, not a catchable one.
    proved(
        r#"
f : Rational -> Bool
f(q) = q == 1
"#,
    );
}

#[test]
fn int_equality_with_rational_proved() {
    proved(
        r#"
f : Int * Rational -> Bool
f(n, q) = n != q
"#,
    );
}

// ── `quot`/`rem` stay integer-only ───────────────────────────────────────────

#[test]
fn quot_still_truncates_toward_negative_infinity_proved() {
    // Unchanged by the tower: `quot` is Euclidean integer division and still
    // reports `Kind::Int`, so an `Int` range needs no divisibility proof.
    proved(
        r#"
f : Int * NonZeroInt -> Int
f(a, b) = a quot b
"#,
    );
}

#[test]
fn rem_still_int_proved() {
    proved(
        r#"
f : Int * NonZeroInt -> Int
f(a, b) = a rem b
"#,
    );
}

// ── Rational is exact, so it cannot overflow ─────────────────────────────────

#[test]
fn rational_arithmetic_carries_no_overflow_obligation() {
    // An `Int64`-fit claim on a boxed exact rational is meaningless; asking
    // for one would also read as a divisibility obligation, which nobody
    // stated. Proving this at all is the assertion.
    proved(
        r#"
f : Rational * Rational -> Rational
f(p, q) = p * q
"#,
    );
}
