use super::helpers::*;

// Tests for three related features:
//   1. Repeated products  — `X * N` is sugar for `X * ... * X` (N copies)
//   2. Homogeneous arrays — `[1, 2, 3]` value literal with compile-time kind check
//   3. Kleene-star sets   — `X*` = `{} | X | X*X | X*X*X | ...`
// TODO: remove all #[ignore] gates in this file once the features are solver-ready.

// ── Repeated products (`X * N`) ───────────────────────────────────────────────

// Int * 3 → Int * Int * Int; summing three Ints stays in Int.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_int3_sum_proved() {
    proved("
f : Int * 3 -> Int
f(x, y, z) = x + y + z
");
}

// Nat * 3 → Nat * Nat * Nat; summing three Nats stays in Nat.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_nat3_sum_proved() {
    proved("
f : Nat * 3 -> Nat
f(x, y, z) = x + y + z
");
}

// Nat * 2; subtraction can go negative — Nat range fails.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_nat2_diff_counterexample() {
    counterexample("
f : Nat * 2 -> Nat
f(x, y) = x - y
");
}

// Int * 3 in range: returning a 3-tuple of Ints from an Int domain.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_range_tuple_proved() {
    proved("
f : Int -> Int * 3
f(x) = [x, x + 1, x + 2]
");
}

// Nat * 3 in range: the literal [1, 2, 3] is a valid element.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_range_literal_proved() {
    proved("
f : -> Nat * 3
f() = [1, 2, 3]
");
}

// Nat * 3 range with a negative element: counterexample.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_range_negative_element_counterexample() {
    counterexample("
f : -> Nat * 3
f() = [1, -1, 3]
");
}

// Int * 2 range: projection of a pair is proved.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_projection_proved() {
    proved("
fst : Int * 2 -> Int
fst(t) = t.0
");
}

// Nat * 2 range: projecting an element is still in Nat.
#[test]
#[ignore = "X * N repeated-product not yet implemented in solver"]
fn repeated_product_nat_pair_proj_proved() {
    proved("
fst : Nat * 2 -> Nat
fst(t) = t.0
");
}

// ── Homogeneous array literals (`[...]`) ──────────────────────────────────────

// [1, 2, 3] satisfies Int * 3 range.
#[test]
#[ignore = "array literal syntax not yet implemented in solver"]
fn array_lit_nat_elements_proved() {
    proved("
f : -> Nat * 3
f() = [1, 2, 3]
");
}

// [1, 2, 3, 4, 5] satisfies Nat * 5 range.
#[test]
#[ignore = "array literal syntax not yet implemented in solver"]
fn array_lit_five_elements_proved() {
    proved("
f : -> Nat * 5
f() = [1, 2, 3, 4, 5]
");
}

// Elements computed from a parameter; result is in Int * 3.
#[test]
#[ignore = "array literal syntax not yet implemented in solver"]
fn array_lit_computed_elements_proved() {
    proved("
f : Int -> Int * 3
f(x) = [x, x + 1, x - 1]
");
}

// Nat * 3 range but one element is negative: counterexample.
#[test]
#[ignore = "array literal syntax not yet implemented in solver"]
fn array_lit_out_of_range_element_counterexample() {
    counterexample("
f : -> Nat * 3
f() = [1, 2, -1]
");
}

// [true, false, true] is a valid Bool * 3 value.
#[test]
#[ignore = "array literal syntax not yet implemented in solver"]
fn array_lit_bool_elements_proved() {
    proved("
f : -> Bool * 3
f() = [true, false, true]
");
}

// [] is the empty array — valid element of X* for any X.
#[test]
#[ignore = "array literal syntax / Kleene-star not yet implemented in solver"]
fn array_lit_empty_in_kleene_range_proved() {
    proved("
f : -> Nat*
f() = []
");
}

// ── Kleene-star sets (`X*`) ───────────────────────────────────────────────────
// X* = {} | X | X*X | X*X*X | ...

// The empty tuple [] is in Nat* (the {} arm).
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_empty_tuple_proved() {
    proved("
f : -> Nat*
f() = []
");
}

// A single-element array [3] is in Nat* (the Nat arm).
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_single_element_proved() {
    proved("
f : -> Nat*
f() = [3]
");
}

// [1, 2, 3] is in Nat* (the Nat*Nat*Nat arm).
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_three_elements_proved() {
    proved("
f : -> Nat*
f() = [1, 2, 3]
");
}

// A negative element is not in Nat, so [-1] ∉ Nat*.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_negative_element_counterexample() {
    proved("
f : -> Nat*
f() = [-1]
");
}

// Int* allows negative elements; [-1, 0, 1] ∈ Int*.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_int_star_negative_allowed_proved() {
    proved("
f : -> Int*
f() = [-1, 0, 1]
");
}

// Identity on Nat*: taking a Nat* and returning it as Nat*.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_identity_proved() {
    proved("
f : Nat* -> Nat*
f(xs) = xs
");
}

// A NatPos* value satisfies Nat* (NatPos ⊆ Nat element-wise).
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_natpos_star_into_nat_star_proved() {
    proved("
f : NatPos* -> Nat*
f(xs) = xs
");
}

// Nat* does not guarantee NatPos* (0 could be an element).
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_nat_star_not_natpos_star_counterexample() {
    counterexample("
f : Nat* -> NatPos*
f(xs) = xs
");
}

// A function accepting X* and returning the length as a Nat.
// (len is a built-in that returns the number of elements.)
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_len_is_nat_proved() {
    proved("
f : Nat* -> Nat
f(xs) = len(xs)
");
}

// (Int - {0})* — Kleene star of a non-zero integer set.
// Any element of the vector is non-zero.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented in solver"]
fn kleene_set_difference_star_proved() {
    proved("
f : (Int - {0})* -> Int*
f(xs) = xs
");
}
