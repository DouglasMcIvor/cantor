use super::helpers::*;

// ── IntN ranges ───────────────────────────────────────────────────────────────

#[test]
fn int16_identity_stays_int16() {
    proved("id16 : Int16 -> Int16\nid16(x) = x");
}

#[test]
fn int16_double_overflows() {
    counterexample("double16 : Int16 -> Int16\ndouble16(x) = x + x");
}

// ── Set expressions in signatures ─────────────────────────────────────────────

#[test]
fn set_difference_domain_proved() {
    proved("
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y
");
}

#[test]
fn set_difference_single_arg_proved() {
    proved("
sign : NatPos - {0} -> NatPos
sign(x) = 1
");
}

#[test]
fn singleton_set_range_proved() {
    proved("
constant42 : Int -> {42}
constant42(x) = 42
");
}

#[test]
fn singleton_set_range_counterexample() {
    counterexample("
not_constant : Int -> {42}
not_constant(x) = x
");
}

#[test]
fn singleton_domain_proved() {
    proved("
succ_zero : {0} -> NatPos
succ_zero(x) = x + 1
");
}

#[test]
fn set_union_domain_proved() {
    proved("
widen : Int8 | Int16 -> Int
widen(x) = x
");
}

#[test]
fn set_intersection_domain_proved() {
    proved("
narrow : Nat & Int16 -> Nat
narrow(x) = x
");
}

#[test]
fn multi_element_set_lit_range_proved() {
    proved("
bool_to_bit : Int -> {0, 1}
bool_to_bit(x) = if x == 0 then 0 else 1
");
}

#[test]
fn multi_element_set_lit_range_counterexample() {
    counterexample("
bad_bit : Int -> {0, 1}
bad_bit(x) = x + x
");
}

#[test]
fn safe_div_fixture_all_proved() {
    let src = "
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y

positive_div : NatPos * NatPos -> Nat
positive_div(x, y) = x / y
";
    for (_fn_name, sig_results) in check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, CheckResult::Proved, "`{label}` should be Proved");
        }
    }
}

// ── NonZeroInt named set ──────────────────────────────────────────────────────

#[test]
fn nonzeroint_domain_proved() {
    proved("
safe_recip : NonZeroInt -> Int
safe_recip(x) = 1 / x
");
}

#[test]
fn nonzeroint_two_arg_proved() {
    proved("
safe_div : Int * NonZeroInt -> Int
safe_div(x, y) = x / y
");
}

#[test]
fn nonzeroint_range_proved() {
    proved("
nonzero_shift : Int -> NonZeroInt
nonzero_shift(x) = x + 1 + (if x >= 0 then 1 else -1)
");
}

#[test]
fn nonzeroint_range_counterexample() {
    counterexample("
bad_range : Int -> NonZeroInt
bad_range(x) = x
");
}

#[test]
fn nonzeroint_equivalent_to_set_diff() {
    let src_named  = "safe_div : Int * NonZeroInt -> Int\nsafe_div(x, y) = x / y";
    let src_inline = "safe_div : Int * (Int - {0}) -> Int\nsafe_div(x, y) = x / y";
    proved(src_named);
    proved(src_inline);
}

#[test]
fn division_natpos_domain_proved() {
    proved("
inv_floor : NatPos -> Nat
inv_floor(x) = 10 / x
");
}

#[test]
fn division_guarded_by_if_proved() {
    proved("
guarded_div : Int -> Int
guarded_div(x) = if x != 0 then 10 / x else 0
");
}

#[test]
fn division_guarded_wrong_branch_counterexample() {
    counterexample("
bad_guard : Int -> Int
bad_guard(x) = if x == 0 then 10 / x else 0
");
}

// ── Set comprehensions ────────────────────────────────────────────────────────

#[test]
fn comprehension_literal_source_as_range_proved() {
    // Range is a comprehension: value must equal 2*x for some x in {1,3,5}.
    proved("
f : Int -> {x * 2 for x in {1, 3, 5}}
f(n) = 6
");
}

#[test]
fn comprehension_literal_source_as_range_counterexample() {
    counterexample("
f : Int -> {x * 2 for x in {1, 3, 5}}
f(n) = 5
");
}

#[test]
fn comprehension_with_filter_as_range_proved() {
    // {x for x in {1,2,3,4,5} if x > 2} = {3, 4, 5}
    proved("
f : Int -> {x for x in {1, 2, 3, 4, 5} if x > 2}
f(n) = 4
");
}

#[test]
fn comprehension_with_filter_as_range_counterexample() {
    counterexample("
f : Int -> {x for x in {1, 2, 3, 4, 5} if x > 2}
f(n) = 2
");
}

#[test]
fn comprehension_identity_named_source_as_domain_proved() {
    // Domain is {x for x in Nat if x > 5} — i.e. integers > 5.
    proved("
f : {x for x in Nat if x > 5} -> NatPos
f(n) = n
");
}

#[test]
fn comprehension_identity_named_source_as_domain_counterexample() {
    // The domain includes 6 but the range Nat excludes negative results.
    // Body returns n - 10 which is negative for n=6..9.
    counterexample("
f : {x for x in Nat if x > 5} -> NatPos
f(n) = n - 10
");
}

#[test]
fn comprehension_in_membership_assert_proved() {
    // `assert y in {x * 2 for x in {1, 3, 5}}` where y = 6 is statically proved.
    proved("
f : Int -> Nat
f(n) {
    mut y: Nat = 6
    assume y in {x * 2 for x in {1, 3, 5}}
    y
}
");
}
