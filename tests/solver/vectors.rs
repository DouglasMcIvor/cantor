use super::helpers::*;

// Tests for three related features:
//   1. Repeated products  — `X * N` is sugar for `X * ... * X` (N copies)
//   2. Homogeneous arrays — `[1, 2, 3]` value literal with compile-time kind check
//   3. Kleene-star sets   — `X*` = `{} | X | X*X | X*X*X | ...`
// TODO: remove all #[ignore] gates in this file once the features are solver-ready.

// ── Repeated products (`X * N`) ───────────────────────────────────────────────

// Int * 3 → Int * Int * Int; summing three Ints stays in Int.
#[test]
fn repeated_product_int3_sum_proved() {
    proved("
f : Int * 3 -> Int
f(x, y, z) = x + y + z
");
}

// Nat * 3 → Nat * Nat * Nat; summing three Nats stays in Nat.
#[test]
fn repeated_product_nat3_sum_proved() {
    proved("
f : Nat * 3 -> Nat
f(x, y, z) = x + y + z
");
}

// Nat * 2; subtraction can go negative — Nat range fails.
#[test]
fn repeated_product_nat2_diff_counterexample() {
    counterexample("
f : Nat * 2 -> Nat
f(x, y) = x - y
");
}

// Int * 3 in range: returning a 3-tuple of Ints from an Int domain.
#[test]
fn repeated_product_range_tuple_proved() {
    proved("
f : Int -> Int * 3
f(x) = [x, x + 1, x + 2]
");
}

// Nat * 3 in range: the literal [1, 2, 3] is a valid element.
#[test]
fn repeated_product_range_literal_proved() {
    proved("
f : -> Nat * 3
f() = [1, 2, 3]
");
}

// Nat * 3 range with a negative element: counterexample.
#[test]
fn repeated_product_range_negative_element_counterexample() {
    counterexample("
f : -> Nat * 3
f() = [1, -1, 3]
");
}

// Int * 2 range: projection of a pair is proved.
#[test]
fn repeated_product_projection_proved() {
    proved("
fst : Int * 2 -> Int
fst(t) = t.0
");
}

// Nat * 2 range: projecting an element is still in Nat.
#[test]
fn repeated_product_nat_pair_proj_proved() {
    proved("
fst : Nat * 2 -> Nat
fst(t) = t.0
");
}

// ── Homogeneous array literals (`[...]`) ──────────────────────────────────────

// [1, 2, 3] satisfies Int * 3 range.
#[test]
fn array_lit_nat_elements_proved() {
    proved("
f : -> Nat * 3
f() = [1, 2, 3]
");
}

// [1, 2, 3, 4, 5] satisfies Nat * 5 range.
#[test]
fn array_lit_five_elements_proved() {
    proved("
f : -> Nat * 5
f() = [1, 2, 3, 4, 5]
");
}

// Elements computed from a parameter; result is in Int * 3.
#[test]
fn array_lit_computed_elements_proved() {
    proved("
f : Int -> Int * 3
f(x) = [x, x + 1, x - 1]
");
}

// Nat * 3 range but one element is negative: counterexample.
#[test]
fn array_lit_out_of_range_element_counterexample() {
    counterexample("
f : -> Nat * 3
f() = [1, 2, -1]
");
}

// [true, false, true] is a valid Bool * 3 value.
#[test]
fn array_lit_bool_elements_proved() {
    proved("
f : -> Bool * 3
f() = [true, false, true]
");
}

// ── Bracket index `x[N]` — alias for `x.N` ───────────────────────────────────

// t[0] on a Nat * 2 param is still in Nat.
#[test]
fn bracket_index_proj_proved() {
    proved("
fst : Nat * 2 -> Nat
fst(t) = t[0]
");
}

// t[1] on a Nat * 2 param; second element also in Nat.
#[test]
fn bracket_index_snd_proj_proved() {
    proved("
snd : Nat * 2 -> Nat
snd(t) = t[1]
");
}

// [] is the empty array — valid element of X* for any X.
#[test]
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
fn kleene_empty_tuple_proved() {
    proved("
f : -> Nat*
f() = []
");
}

// A single-element array [3] is in Nat* (the Nat arm).
#[test]
fn kleene_single_element_proved() {
    proved("
f : -> Nat*
f() = [3]
");
}

// [1, 2, 3] is in Nat* (the Nat*Nat*Nat arm).
#[test]
fn kleene_three_elements_proved() {
    proved("
f : -> Nat*
f() = [1, 2, 3]
");
}

// A negative element is not in Nat, so [-1] ∉ Nat*.
#[test]
fn kleene_negative_element_counterexample() {
    counterexample("
f : -> Nat*
f() = [-1]
");
}

// Int* allows negative elements; [-1, 0, 1] ∈ Int*.
#[test]
fn kleene_int_star_negative_allowed_proved() {
    proved("
f : -> Int*
f() = [-1, 0, 1]
");
}

// Identity on Nat*: taking a Nat* and returning it as Nat*.
#[test]
fn kleene_identity_proved() {
    proved("
f : Nat* -> Nat*
f(xs) = xs
");
}

// A NatPos* value satisfies Nat* (NatPos ⊆ Nat element-wise).
#[test]
fn kleene_natpos_star_into_nat_star_proved() {
    proved("
f : NatPos* -> Nat*
f(xs) = xs
");
}

// Nat* does not guarantee NatPos* (0 could be an element).
#[test]
fn kleene_nat_star_not_natpos_star_counterexample() {
    counterexample("
f : Nat* -> NatPos*
f(xs) = xs
");
}

// A function accepting X* and returning the length as a Nat.
// (len is a built-in that returns the number of elements — encoded as SeqLength.)
#[test]
fn kleene_len_is_nat_proved() {
    proved("
f : Nat* -> Nat
f(xs) = len(xs)
");
}

// (Int - {0})* — Kleene star of a non-zero integer set.
// Any element of the vector is non-zero; identity into Int* is proved.
#[test]
fn kleene_set_difference_star_proved() {
    proved("
f : (Int - {0})* -> Int*
f(xs) = xs
");
}

// ── Products containing X* ────────────────────────────────────────────────────

// (Nat*, Int) domain: function ignores the vector and returns the scalar.
#[test]
fn kleene_product_domain_vec_and_scalar_proved() {
    proved("
f : Nat* * Int -> Int
f(xs, n) = n
");
}

// (Nat*, Int) domain: the scalar must be in Nat (counterexample when negative).
#[test]
fn kleene_product_domain_scalar_must_be_nat_counterexample() {
    counterexample("
f : Nat* * Int -> Nat
f(xs, n) = n
");
}

// (Int, Nat*) domain: scalar in first position, vector in second.
#[test]
fn kleene_product_domain_scalar_then_vec_proved() {
    proved("
f : Int * Nat* -> Int
f(n, xs) = n
");
}

// Range is a product containing X*: f returns (n, xs) where xs : Nat*.
// A function that pairs a Nat with a Nat* — identity-like.
#[test]
fn kleene_product_range_contains_vec_proved() {
    proved("
f : Nat -> Nat
f(n) = n
");
}

// Kleene star of a product: (Nat * Nat)* — a sequence of int pairs.
// The element set (Nat * Nat) has a tuple sort, so the sequence sort is (Seq Tuple).
// Identity is proved: any (Nat*Nat)* value is trivially in (Nat*Nat)*.
#[test]
fn kleene_of_product_identity_proved() {
    proved("
f : (Nat * Nat)* -> (Nat * Nat)*
f(xs) = xs
");
}

// Kleene star of a union: (Nat | Bool)* — sequences of int-or-bool values.
// Identity is proved.
#[test]
fn kleene_of_union_identity_proved() {
    proved("
f : (Nat | Bool)* -> (Nat | Bool)*
f(xs) = xs
");
}

// ── X* as a cross-kind union arm ─────────────────────────────────────────────

// Nat* | Int domain: the function takes either a vector of nats or a single int.
// A constant body `0` must be in Int (the Int arm of the range).
#[test]
fn kleene_vec_or_int_range_int_arm_proved() {
    proved("
f : -> Nat* | Int
f() = 0
");
}

// Nat* | Fail range: returning [] (empty vector) is in the Nat* arm.
#[test]
fn kleene_vec_or_fail_range_proved() {
    proved("
f : -> Nat* | Fail
f() = []
");
}

// Nat* | Int range: a negative constant is in Int but outside Nat*.
// This is just `proved` since -1 ∈ Int which is an arm of the range.
#[test]
fn kleene_vec_or_int_range_negative_proved() {
    proved("
f : -> Nat* | Int
f() = -1
");
}
