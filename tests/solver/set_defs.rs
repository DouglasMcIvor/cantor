use super::helpers::*;

// ── Alias sets in domain/range ────────────────────────────────────────────────

#[test]
fn alias_set_literal_in_range_proved() {
    proved("
Colour = {1, 2, 3}
red : -> Colour
red() = 1
");
}

#[test]
fn alias_set_literal_in_range_counterexample() {
    counterexample("
Colour = {1, 2, 3}
bad_colour : -> Colour
bad_colour() = 4
");
}

#[test]
fn alias_named_set_in_domain_proved() {
    proved("
MyNat = alias Nat
inc : MyNat -> MyNat
inc(x) = x + 1
");
}

#[test]
fn alias_named_set_in_domain_counterexample() {
    counterexample("
MyNat = alias Nat
negate : MyNat -> MyNat
negate(x) = -x
");
}

#[test]
fn alias_union_in_range_proved() {
    proved("
SmallPrime = {2, 3, 5, 7}
val : -> SmallPrime
val() = 5
");
}

#[test]
fn transitive_alias_proved() {
    proved("
Inner = {10, 20}
Outer = alias Inner
f : -> Outer
f() = 10
");
}

// ── Distinct sets → Unknown ───────────────────────────────────────────────────

#[test]
fn distinct_set_domain_unknown() {
    unknown("
Litre = distinct Nat
volume : Litre -> Litre
volume(x) = x
");
}

#[test]
fn distinct_set_range_unknown() {
    unknown("
Kelvin = distinct NatPos
freeze : -> Kelvin
freeze() = 273
");
}
