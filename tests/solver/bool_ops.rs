use super::helpers::*;

// ── Valid uses of and / or / not ─────────────────────────────────────────────

#[test]
fn bool_and_proved() {
    proved("
f : Bool * Bool -> Bool
f(x, y) = x and y
");
}

#[test]
fn bool_or_proved() {
    proved("
f : Bool * Bool -> Bool
f(x, y) = x or y
");
}

#[test]
fn bool_not_proved() {
    proved("
f : Bool -> Bool
f(x) = not x
");
}

#[test]
fn bool_chained_proved() {
    proved("
f : Bool * Bool -> Bool
f(x, y) = (not x) and (not y)
");
}

// ── Domain violations: non-Bool operands ─────────────────────────────────────

// `and` requires both args in Bool; Nat values may be outside {0, 1}.
#[test]
fn and_nat_operand_counterexample() {
    counterexample("
f : Nat * Nat -> Bool
f(x, y) = x and y
");
}

// `or` requires both args in Bool.
#[test]
fn or_nat_operand_counterexample() {
    counterexample("
f : Nat * Nat -> Bool
f(x, y) = x or y
");
}

// `not` requires its operand in Bool.
#[test]
fn not_nat_operand_counterexample() {
    counterexample("
f : Nat -> Bool
f(x) = not x
");
}

// A value of a distinct set is never in Bool.
#[test]
fn and_distinct_operand_counterexample() {
    counterexample("
Colour = distinct Nat
f : Colour * Colour -> Bool
f(x, y) = x and y
");
}

#[test]
fn not_distinct_operand_counterexample() {
    counterexample("
Colour = distinct Nat
f : Colour -> Bool
f(x) = not x
");
}
