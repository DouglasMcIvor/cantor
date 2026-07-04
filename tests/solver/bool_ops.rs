use super::helpers::*;

// ── Valid uses of and / or / not ─────────────────────────────────────────────

#[test]
fn bool_and_proved() {
    proved(
        "
f : Bool * Bool -> Bool
f(x, y) = x and y
",
    );
}

#[test]
fn bool_or_proved() {
    proved(
        "
f : Bool * Bool -> Bool
f(x, y) = x or y
",
    );
}

#[test]
fn bool_not_proved() {
    proved(
        "
f : Bool -> Bool
f(x) = not x
",
    );
}

#[test]
fn bool_chained_proved() {
    proved(
        "
f : Bool * Bool -> Bool
f(x, y) = (not x) and (not y)
",
    );
}

// ── Domain violations: non-Bool operands ─────────────────────────────────────

// `and` requires both args in Bool; Nat values may be outside {0, 1}.
#[test]
fn and_nat_operand_counterexample() {
    counterexample(
        "
f : Nat * Nat -> Bool
f(x, y) = x and y
",
    );
}

// `or` requires both args in Bool.
#[test]
fn or_nat_operand_counterexample() {
    counterexample(
        "
f : Nat * Nat -> Bool
f(x, y) = x or y
",
    );
}

// `not` requires its operand in Bool.
#[test]
fn not_nat_operand_counterexample() {
    counterexample(
        "
f : Nat -> Bool
f(x) = not x
",
    );
}

// A value of a distinct set is never in Bool.
#[test]
fn and_distinct_operand_counterexample() {
    counterexample(
        "
Colour = distinct Nat
f : Colour * Colour -> Bool
f(x, y) = x and y
",
    );
}

#[test]
fn not_distinct_operand_counterexample() {
    counterexample(
        "
Colour = distinct Nat
f : Colour -> Bool
f(x) = not x
",
    );
}

// ── Cross-kind comparisons are rejected at elaboration ───────────────────────
//
// Bool and Int are disjoint value families (`true` is not `1`). Before the
// elaborate-level check these reached cvc5 as ill-sorted terms and aborted
// the whole process with a raw C++ error.

#[test]
fn eq_bool_int_rejected() {
    rejected(
        "
f : Int -> Bool
f(x) = x == true
",
    );
}

#[test]
fn ordering_bool_operand_rejected() {
    rejected(
        "
f : Int * Bool -> Bool
f(x, b) = x < b
",
    );
}

// `a < b < c` parses as `(a < b) < c`, so the second `<` sees a Bool operand —
// rejected with a hint to write `a < b and b < c`.
#[test]
fn chained_comparison_rejected() {
    rejected(
        "
f : Int * Int * Int -> Bool
f(a, b, c) = a < b < c
",
    );
}
