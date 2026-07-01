use super::helpers::*;

// Tests for all four set-expression operators (|, -, ^, +) in both domain and
// range positions.  These are the cases that currently fall through to "integer"
// in the CVC5 sort encoding; until the encoding is fixed many of the
// counterexample cases will incorrectly return Proved.

// ── Union (|) in domain ───────────────────────────────────────────────────────

// Nat | NatPos = Nat; identity into Nat is proved.
#[test]
fn union_domain_nat_or_natpos_to_nat_proved() {
    proved("
f : Nat | NatPos -> Nat
f(x) = x
");
}

// x from Nat | {-1} can be -1, which is not in NatPos.
#[test]
fn union_domain_nat_or_neg_to_natpos_counterexample() {
    counterexample("
f : Nat | {-1} -> NatPos
f(x) = x
");
}

// x from Nat | {-1} is always in Int.
#[test]
fn union_domain_nat_or_neg_to_int_proved() {
    proved("
f : Nat | {-1} -> Int
f(x) = x
");
}

// Int8 | Int16 in domain with arithmetic; result fits in Int.
#[test]
fn union_domain_arithmetic_proved() {
    proved("
f : Int8 | Int16 -> Int
f(x) = x + 1
");
}

// ── Union (|) in range ────────────────────────────────────────────────────────

// An Int8 value satisfies Int8 | Int16.
#[test]
fn union_range_from_int8_proved() {
    proved("
f : Int8 -> Int8 | Int16
f(x) = x
");
}

// An Int16 value satisfies Int8 | Int16.
#[test]
fn union_range_from_int16_proved() {
    proved("
f : Int16 -> Int8 | Int16
f(x) = x
");
}

// A plain Int can be outside both Int8 and Int16.
#[test]
fn union_range_from_int_counterexample() {
    counterexample("
bad : Int -> Int8 | Int16
bad(x) = x
");
}

// -1 satisfies the Nat | {-1} range.
#[test]
fn union_range_literal_neg_one_proved() {
    proved("
f : -> Nat | {-1}
f() = -1
");
}

// 0 satisfies the Nat | {-1} range (0 is in Nat).
#[test]
fn union_range_zero_proved() {
    proved("
f : -> Nat | {-1}
f() = 0
");
}

// -2 is not in Nat | {-1}.
#[test]
fn union_range_neg_two_counterexample() {
    counterexample("
f : -> Nat | {-1}
f() = -2
");
}

// NatPos values satisfy Nat | {-1} since NatPos ⊆ Nat.
#[test]
fn union_range_natpos_into_nat_or_neg_proved() {
    proved("
f : NatPos -> Nat | {-1}
f(x) = x
");
}

// ── Set difference (-) in domain ─────────────────────────────────────────────

// Nat - {0} = NatPos; identity into NatPos is proved.
#[test]
fn diff_domain_nat_minus_zero_to_natpos_proved() {
    proved("
f : Nat - {0} -> NatPos
f(x) = x
");
}

// x ∈ Nat - {0} so x ≥ 1; x - 1 ≥ 0 ∈ Nat.
#[test]
fn diff_domain_pred_to_nat_proved() {
    proved("
pred : Nat - {0} -> Nat
pred(x) = x - 1
");
}

// x - 1 = 0 when x = 1; NatPos range fails.
#[test]
fn diff_domain_pred_to_natpos_counterexample() {
    counterexample("
pred : Nat - {0} -> NatPos
pred(x) = x - 1
");
}

// Int - {0} excludes zero so the denominator is safe.
#[test]
fn diff_domain_safe_recip_proved() {
    proved("
recip : Int - {0} -> Int
recip(x) = 1 / x
");
}

// Int - {0} * Int - {0}: division safe as both args are non-zero.
#[test]
fn diff_domain_two_arg_safe_div_proved() {
    proved("
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y
");
}

// ── Set difference (-) in range ───────────────────────────────────────────────

// NatPos ⊆ Int - {0}; returning a NatPos value into Int - {0} is proved.
#[test]
fn diff_range_natpos_proved() {
    proved("
f : NatPos -> Int - {0}
f(x) = x
");
}

// 0 ∈ Nat but 0 ∉ Int - {0}; identity from Nat fails.
#[test]
fn diff_range_nat_counterexample() {
    counterexample("
bad : Nat -> Int - {0}
bad(x) = x
");
}

// The constant 1 is always in Int - {0}.
#[test]
fn diff_range_constant_one_proved() {
    proved("
one : -> Int - {0}
one() = 1
");
}

// The constant 0 is never in Int - {0}.
#[test]
fn diff_range_constant_zero_counterexample() {
    counterexample("
zero : -> Int - {0}
zero() = 0
");
}

// NatPos + NatPos ≥ 2 > 0, so the sum lies in Nat - {0}.
#[test]
fn diff_range_sum_natpos_to_nat_minus_zero_proved() {
    proved("
sum : NatPos * NatPos -> Nat - {0}
sum(x, y) = x + y
");
}

// Returning a Nat - {0} value back into Nat - {0}: identity proved.
#[test]
fn diff_range_identity_proved() {
    proved("
f : Nat - {0} -> Nat - {0}
f(x) = x
");
}

// x - 1 where x ∈ Nat - {0}: can be 0 when x = 1, so Nat - {0} fails.
#[test]
fn diff_range_pred_counterexample() {
    counterexample("
bad : Nat - {0} -> Nat - {0}
bad(x) = x - 1
");
}

// ── Symmetric difference (^) in domain ───────────────────────────────────────

// Nat ^ {0} = NatPos; arithmetic x + 1 ≥ 2, NatPos proved.
#[test]
fn sym_diff_domain_add_one_proved() {
    proved("
succ : Nat ^ {0} -> NatPos
succ(x) = x + 1
");
}

// x ∈ Nat ^ {0} = NatPos, so x - 1 ≥ 0 ∈ Nat.
#[test]
fn sym_diff_domain_pred_to_nat_proved() {
    proved("
pred : Nat ^ {0} -> Nat
pred(x) = x - 1
");
}

// x - 1 = 0 when x = 1; NatPos range fails.
#[test]
fn sym_diff_domain_pred_to_natpos_counterexample() {
    counterexample("
pred : Nat ^ {0} -> NatPos
pred(x) = x - 1
");
}

// x * 2 where x ∈ NatPos gives ≥ 2 > 0; NatPos range holds.
#[test]
fn sym_diff_domain_double_proved() {
    proved("
double : Nat ^ {0} -> NatPos
double(x) = x * 2
");
}

// ── Symmetric difference (^) in range ────────────────────────────────────────

// NatPos = Nat ^ {0}; returning a NatPos value is proved.
#[test]
fn sym_diff_range_natpos_proved() {
    proved("
f : NatPos -> Nat ^ {0}
f(x) = x
");
}

// 0 ∈ Nat but 0 ∉ Nat ^ {0}; identity from Nat fails.
#[test]
fn sym_diff_range_nat_counterexample() {
    counterexample("
bad : Nat -> Nat ^ {0}
bad(x) = x
");
}

// x + 1 from NatPos gives ≥ 2, still in NatPos = Nat ^ {0}.
#[test]
fn sym_diff_range_succ_proved() {
    proved("
succ : NatPos -> Nat ^ {0}
succ(x) = x + 1
");
}

// Returning a Nat ^ {0} value back into Nat ^ {0}: identity proved.
#[test]
fn sym_diff_range_identity_proved() {
    proved("
f : Nat ^ {0} -> Nat ^ {0}
f(x) = x
");
}

// Returning 0 from any domain into Nat ^ {0} always fails.
#[test]
fn sym_diff_range_constant_zero_counterexample() {
    counterexample("
bad : NatPos -> Nat ^ {0}
bad(x) = 0
");
}

// ── Disjoint union (+) in domain ─────────────────────────────────────────────

// x : {0} + NatPos = Nat; x + 1 ≥ 1 ∈ NatPos.
#[test]
fn disjoint_domain_add_one_to_natpos_proved() {
    proved("
succ : {0} + NatPos -> NatPos
succ(x) = x + 1
");
}

// Two args: x ∈ {0} + NatPos = Nat, y ∈ NatPos; x + y ≥ 1.
#[test]
fn disjoint_domain_two_arg_sum_proved() {
    proved("
f : ({0} + NatPos) * NatPos -> NatPos
f(x, y) = x + y
");
}

// ── Disjoint union (+) in range ───────────────────────────────────────────────

// 0 ∈ {0}; satisfies {0} + NatPos range.
#[test]
fn disjoint_range_zero_proved() {
    proved("
f : -> {0} + NatPos
f() = 0
");
}

// NatPos values satisfy the NatPos arm of {0} + NatPos.
#[test]
fn disjoint_range_natpos_proved() {
    proved("
f : NatPos -> {0} + NatPos
f(x) = x
");
}

// -1 is not in {0} + NatPos.
#[test]
fn disjoint_range_neg_one_counterexample() {
    counterexample("
f : -> {0} + NatPos
f() = -1
");
}

// Plain Int input — negative values break {0} + NatPos range.
#[test]
fn disjoint_range_int_counterexample() {
    counterexample("
bad : Int -> {0} + NatPos
bad(x) = x
");
}

// ── Cross-operator combinations ───────────────────────────────────────────────

// (Nat - {0}) | {0} = Nat; identity into Nat proved.
#[test]
fn cross_diff_or_zero_covers_nat_proved() {
    proved("
f : (Nat - {0}) | {0} -> Nat
f(x) = x
");
}

// ── Cross-sort symmetric difference (^) — NOT YET SUPPORTED ─────────────────
// When the LHS and RHS of `^` have different CVC5 sorts (e.g. Seq(Int) vs Int,
// or tuple sort vs Int), `set_sort` currently panics with a TODO.
// These tests document the intended semantics.  Un-ignore once `set_sort` builds
// the cross-kind union sort for SymDiff (same DT machinery as cross-kind `|`).
//
// Semantics under sequence unification:
//   Nat* ^ Int = (Nat* - Int) ∪ (Int - Nat*)
//             = (sequences of length ≠ 1) ∪ ∅    -- Int ⊆ Nat* so Int - Nat* = ∅
//             = sequences of length ≠ 1
//
//   (Nat * Nat) ^ Int = (Nat*Nat - Int) ∪ (Int - Nat*Nat)
//                     = (2-element sequences) ∪ ∅   -- Nat*Nat ⊆ Nat* and Int ⊆ Nat*;
//                                                        Int has length 1 ≠ 2, so disjoint
//                     = length-2 sequences with Nat elements
//
//   Bool ^ Nat = (Bool - Nat) ∪ (Nat - Bool) -- Bool and Nat are disjoint (no
//              implicit 0/1 conversion), so Bool - Nat = Bool and Nat - Bool = Nat
//              = Bool | Nat (a tagged union, same as `+`)
//   NOTE: the two tests below (`cross_sort_sym_diff_bool_nat_*`) predate this
//   correction and still assume the old "Bool ⊆ Nat" semantics in their bodies
//   (`x + 1` on a possibly-Bool-sorted `x`) — they'll need rewriting, not just
//   un-ignoring, once cross-sort SymDiff is implemented.

// Nat* ^ Int = sequences of length ≠ 1.
// xs[0] + xs[1] is safe because domain guarantees length ≥ 2 (combining with non-empty).
// TODO: requires cross-sort SymDiff in set_sort.
#[test]
#[ignore = "TODO: cross-sort SymDiff (Seq(Int) ^ Int) — set_sort panics; \
            implement cross-kind union sort for SymDiff"]
fn cross_sort_sym_diff_kleene_minus_scalar_proved() {
    proved("
h : (Nat* ^ Int) - {[]} -> Nat
h(xs) = xs[0] + xs[1]
");
}

// Nat* ^ Int = sequences of length ≠ 1; identity back into Nat* is proved.
#[test]
#[ignore = "TODO: cross-sort SymDiff (Seq(Int) ^ Int) — set_sort panics"]
fn cross_sort_sym_diff_kleene_scalar_identity_proved() {
    proved("
f : Nat* ^ Int -> Nat*
f(xs) = xs
");
}

// (Nat * Nat) ^ Int = length-2 Nat sequences; both xs[0] and xs[1] safe.
#[test]
#[ignore = "TODO: cross-sort SymDiff (tuple sort ^ Int) — set_sort panics"]
fn cross_sort_sym_diff_tuple_scalar_proved() {
    proved("
f : (Nat * Nat) ^ Int -> Nat
f(t) = t[0] + t[1]
");
}

// Bool ^ Nat = Nat - {0, 1} = integers ≥ 2.
// x + 1 ≥ 3 is in NatPos; proved.
#[test]
#[ignore = "TODO: cross-sort SymDiff (Bool sort ^ Int sort) — set_sort panics"]
fn cross_sort_sym_diff_bool_nat_succ_proved() {
    proved("
f : Bool ^ Nat -> NatPos
f(x) = x + 1
");
}

// Bool ^ Nat = integers ≥ 2; 0 is not in that set.
#[test]
#[ignore = "TODO: cross-sort SymDiff (Bool sort ^ Int sort) — set_sort panics"]
fn cross_sort_sym_diff_bool_nat_zero_counterexample() {
    counterexample("
bad : NatPos -> Bool ^ Nat
bad(x) = 0
");
}

// Nat ^ {0} and Nat - {0} are both NatPos; identity across operators proved.
#[test]
fn cross_sym_diff_to_set_diff_proved() {
    proved("
f : Nat ^ {0} -> Nat - {0}
f(x) = x
");
}

// Reverse direction: Nat - {0} into Nat ^ {0}.
#[test]
fn cross_set_diff_to_sym_diff_proved() {
    proved("
f : Nat - {0} -> Nat ^ {0}
f(x) = x
");
}

// Multi-operator domain: (Int - {0}) in both args makes division safe.
#[test]
fn cross_two_diff_args_safe_div_proved() {
    proved("
f : (Int - {0}) * (Int - {0}) -> Int
f(x, y) = x / y
");
}

// ── Cross-kind: Bool ∩ integer-valued sets ────────────────────────────────────
// Bool maps to CVC5's boolean sort; integer sets map to CVC5's integer sort.
// Intersection (`&`) is handled correctly today; union (`|`) causes a fatal CVC5
// "expecting a Boolean subexpression" error and is marked #[ignore] until fixed.

// Bool & Nat: Bool = {0,1} ⊆ Nat so Bool & Nat = Bool.
// Identity back into Bool is proved.
#[test]
fn cross_kind_bool_and_nat_to_bool_proved() {
    proved("
f : Bool & Nat -> Bool
f(x) = x
");
}

// Bool & Nat = {0,1}; 0 (= false) is not in NatPos, so counterexample.
#[test]
fn cross_kind_bool_and_nat_to_natpos_counterexample() {
    counterexample("
f : Bool & Nat -> NatPos
f(x) = x
");
}

// Bool and Nat are disjoint (no implicit 0/1 conversion), so Bool & Nat is
// empty — a Bool-domain value can never satisfy it; counterexample.
#[test]
fn cross_kind_bool_to_bool_and_nat_counterexample() {
    counterexample("
f : Bool -> Bool & Nat
f(x) = x
");
}

// Bool & Int: Bool = {0,1} ⊆ Int, so Bool & Int = Bool.
#[test]
fn cross_kind_bool_and_int_to_bool_proved() {
    proved("
f : Bool & Int -> Bool
f(x) = x
");
}

// ── Cross-kind: Bool ∪ integer-valued sets ────────────────────────────────────
// Bool and Int are disjoint (no implicit 0/1 conversion), so `Bool | Nat` is a
// genuine cross-kind union — represented as a CVC5 tagged datatype, the same
// as `(Nat * Nat) | Nat`, not collapsed into plain integer sort.

// A Nat value is wrapped into the Nat arm of the tagged union; proved.
#[test]
fn cross_kind_bool_or_nat_range_from_nat_proved() {
    proved("
f : Nat -> Bool | Nat
f(x) = x
");
}

// A Bool value is wrapped into the Bool arm of the tagged union; proved.
#[test]
fn cross_kind_bool_or_nat_range_from_bool_proved() {
    proved("
f : Bool -> Bool | Nat
f(x) = x
");
}

// A `Bool | Nat`-domain value is a tagged union, not a plain boolean — using
// it directly as an `if` condition needs narrowing that doesn't exist yet, so
// this is rejected at elaboration rather than silently treating the tag/payload
// as a boolean (which is exactly the "Bool ⊆ Int" bug this union sort fixes).
#[test]
fn cross_kind_bool_or_nat_domain_used_as_condition_rejected() {
    rejected("
f : Bool | Nat -> Nat
f(x) = if x then 1 else 0
");
}

// A Nat value like 2 is in Bool | Nat but not in Bool; counterexample.
#[test]
fn cross_kind_bool_or_nat_to_bool_counterexample() {
    counterexample("
bad : Bool | Nat -> Bool
bad(x) = x
");
}

// ── Cross-kind: tuples and scalar sets ───────────────────────────────────────
// A * B maps to a CVC5 tuple sort.  Mixing it with Bool or integer-sort sets
// requires a tagged-union datatype that the solver doesn't yet emit.
// These tests document the intended semantics; un-ignore once fixed.

// Returning a tuple into (Nat * Nat) | Nat range.
// The tuple body (x,x) satisfies the (Nat*Nat) arm; the Nat arm gives
// Constrained(false) for a tuple term (tuples aren't integers), so the
// union resolves to the tuple arm's constraint: x >= 0, which the domain proves.
#[test]
fn cross_kind_nat_to_tuple_or_nat_proved() {
    proved("
f : Nat -> (Nat * Nat) | Nat
f(x) = (x, x)
");
}

// ── Distinct sets in unions ───────────────────────────────────────────────────
// `distinct` sets have an uninterpreted membership predicate (`is_Litre : Int -> Bool`).
// The solver does not automatically know that Litre values satisfy their basis (Nat) —
// it only learns this when constructors or destructors are used.  So `Litre | Nat`
// as a domain is strictly broader than `Nat`: Litre values may fall outside Nat.

// Returning a Litre value into a Litre | Nat range: is_Litre(x) satisfies the Litre arm.
#[test]
fn distinct_in_union_range_proved() {
    proved("
Litre = distinct Nat
f : Litre -> Litre | Nat
f(x) = x
");
}

// Returning a NatPos value into a Litre | Nat range: NatPos ⊆ Nat satisfies the Nat arm.
#[test]
fn scalar_in_distinct_union_range_proved() {
    proved("
Litre = distinct Nat
f : NatPos -> Litre | Nat
f(x) = x
");
}

// Identity from Litre | Nat into Nat: a Litre value is not in Nat so this should
// be a counterexample.
#[test]
fn distinct_union_to_nat_counterexample() {
    counterexample("
Litre = distinct Nat
f : Litre | Nat -> Nat
f(x) = x
");
}

// Two distinct sets based on Nat: a Metre value satisfies the Metre arm of Metre | Litre.
#[test]
fn two_distinct_sets_in_union_proved() {
    proved("
Metre = distinct Nat
Litre = distinct Nat
f : Metre -> Metre | Litre
f(x) = x
");
}

// Metre and Litre are independent uninterpreted predicates; a Metre value need not
// satisfy is_Litre.  Identity from Metre into Litre gives a counterexample.
#[test]
fn two_distinct_sets_cross_arm_counterexample() {
    counterexample("
Metre = distinct Nat
Litre = distinct Nat
f : Metre -> Litre
f(x) = x
");
}

// Constructor wraps a NatPos into Litre, satisfying the Litre arm of Litre | NatPos.
#[test]
fn distinct_constructor_in_union_range_proved() {
    proved("
Litre = distinct Nat
f : NatPos -> Litre | NatPos
f(x) = litre(x)
");
}

// ── Cross-kind: tuple | scalar in domain (needs tagged-union CVC5 sort) ───────
// Creating a parameter variable from a domain like `(Nat * Nat) | Nat` requires a
// single CVC5 sort that can represent both a tuple and an integer — which does not
// These now use the CVC5 algebraic datatype encoding added in Step 6.

// Constant body: should be proved regardless of the cross-kind domain.
#[test]
fn cross_kind_tuple_or_nat_const_proved() {
    proved("
f : (Nat * Nat) | Nat -> Nat
f(x) = 1
");
}

// Identity into Nat should be a counterexample: if x is a tuple, x ∉ Nat.
#[test]
fn cross_kind_tuple_or_nat_domain_identity_counterexample() {
    counterexample("
f : (Nat * Nat) | Nat -> Nat
f(x) = x
");
}

// Arms reversed: Nat | (Nat * Nat) with constant body.
#[test]
fn cross_kind_nat_or_tuple_domain_const_proved() {
    proved("
f : Nat | (Nat * Nat) -> Nat
f(x) = 1
");
}

// Bool | tuple cross-kind domain.
#[test]
fn cross_kind_bool_or_tuple_domain_const_proved() {
    proved("
f : Bool | (Nat * Nat) -> Nat
f(x) = 1
");
}

// ── Kind mismatch: body and range have incompatible kinds ─────────────────────
// Cantor has no type-checking phase, so kind-mismatched programs reach the solver.
// The solver gives a spurious counterexample because
// `membership_constraint(tuple_body, Nat)` returns `Constrained(false)` — a tuple
// can never be an integer — making the range obligation trivially SAT for any model.
// The codegen would catch this mismatch later; the solver does not diagnose it.
#[test]
fn kind_mismatch_tuple_body_scalar_range_counterexample() {
    counterexample("
f : Nat -> Nat
f(x) = (x, x)
");
}
