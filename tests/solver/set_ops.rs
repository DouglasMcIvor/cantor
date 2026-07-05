use super::helpers::*;

// Tests for all four set-expression operators (|, -, ^, +) in both domain and
// range positions.  These are the cases that currently fall through to "integer"
// in the CVC5 sort encoding; until the encoding is fixed many of the
// counterexample cases will incorrectly return Proved.

// ── Union (|) in domain ───────────────────────────────────────────────────────

// Nat | NatPos = Nat; identity into Nat is proved.
#[test]
fn union_domain_nat_or_natpos_to_nat_proved() {
    proved(
        "
f : Nat | NatPos -> Nat
f(x) = x
",
    );
}

// x from Nat | {-1} can be -1, which is not in NatPos.
#[test]
fn union_domain_nat_or_neg_to_natpos_counterexample() {
    counterexample(
        "
f : Nat | {-1} -> NatPos
f(x) = x
",
    );
}

// x from Nat | {-1} is always in Int.
#[test]
fn union_domain_nat_or_neg_to_int_proved() {
    proved(
        "
f : Nat | {-1} -> Int
f(x) = x
",
    );
}

// Int8 | Int16 in domain with arithmetic; result fits in Int.
#[test]
fn union_domain_arithmetic_proved() {
    proved(
        "
f : Int8 | Int16 -> Int
f(x) = x + 1
",
    );
}

// ── Union (|) in range ────────────────────────────────────────────────────────

// An Int8 value satisfies Int8 | Int16.
#[test]
fn union_range_from_int8_proved() {
    proved(
        "
f : Int8 -> Int8 | Int16
f(x) = x
",
    );
}

// An Int16 value satisfies Int8 | Int16.
#[test]
fn union_range_from_int16_proved() {
    proved(
        "
f : Int16 -> Int8 | Int16
f(x) = x
",
    );
}

// A plain Int can be outside both Int8 and Int16.
#[test]
fn union_range_from_int_counterexample() {
    counterexample(
        "
bad : Int -> Int8 | Int16
bad(x) = x
",
    );
}

// -1 satisfies the Nat | {-1} range.
#[test]
fn union_range_literal_neg_one_proved() {
    proved(
        "
f : -> Nat | {-1}
f() = -1
",
    );
}

// 0 satisfies the Nat | {-1} range (0 is in Nat).
#[test]
fn union_range_zero_proved() {
    proved(
        "
f : -> Nat | {-1}
f() = 0
",
    );
}

// -2 is not in Nat | {-1}.
#[test]
fn union_range_neg_two_counterexample() {
    counterexample(
        "
f : -> Nat | {-1}
f() = -2
",
    );
}

// NatPos values satisfy Nat | {-1} since NatPos ⊆ Nat.
#[test]
fn union_range_natpos_into_nat_or_neg_proved() {
    proved(
        "
f : NatPos -> Nat | {-1}
f(x) = x
",
    );
}

// ── Set difference (-) in domain ─────────────────────────────────────────────

// Nat - {0} = NatPos; identity into NatPos is proved.
#[test]
fn diff_domain_nat_minus_zero_to_natpos_proved() {
    proved(
        "
f : Nat - {0} -> NatPos
f(x) = x
",
    );
}

// x ∈ Nat - {0} so x ≥ 1; x - 1 ≥ 0 ∈ Nat.
#[test]
fn diff_domain_pred_to_nat_proved() {
    proved(
        "
pred : Nat - {0} -> Nat
pred(x) = x - 1
",
    );
}

// x - 1 = 0 when x = 1; NatPos range fails.
#[test]
fn diff_domain_pred_to_natpos_counterexample() {
    counterexample(
        "
pred : Nat - {0} -> NatPos
pred(x) = x - 1
",
    );
}

// Int - {0} excludes zero so the denominator is safe.
#[test]
fn diff_domain_safe_recip_proved() {
    proved(
        "
recip : Int - {0} -> Int
recip(x) = 1 / x
",
    );
}

// Int - {0} * Int - {0}: division safe as both args are non-zero.
#[test]
fn diff_domain_two_arg_safe_div_proved() {
    proved(
        "
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y
",
    );
}

// ── Set difference (-) in range ───────────────────────────────────────────────

// NatPos ⊆ Int - {0}; returning a NatPos value into Int - {0} is proved.
#[test]
fn diff_range_natpos_proved() {
    proved(
        "
f : NatPos -> Int - {0}
f(x) = x
",
    );
}

// 0 ∈ Nat but 0 ∉ Int - {0}; identity from Nat fails.
#[test]
fn diff_range_nat_counterexample() {
    counterexample(
        "
bad : Nat -> Int - {0}
bad(x) = x
",
    );
}

// The constant 1 is always in Int - {0}.
#[test]
fn diff_range_constant_one_proved() {
    proved(
        "
one : -> Int - {0}
one() = 1
",
    );
}

// The constant 0 is never in Int - {0}.
#[test]
fn diff_range_constant_zero_counterexample() {
    counterexample(
        "
zero : -> Int - {0}
zero() = 0
",
    );
}

// NatPos + NatPos ≥ 2 > 0, so the sum lies in Nat - {0}.
#[test]
fn diff_range_sum_natpos_to_nat_minus_zero_proved() {
    proved(
        "
sum : NatPos * NatPos -> Nat - {0}
sum(x, y) = x + y
",
    );
}

// Returning a Nat - {0} value back into Nat - {0}: identity proved.
#[test]
fn diff_range_identity_proved() {
    proved(
        "
f : Nat - {0} -> Nat - {0}
f(x) = x
",
    );
}

// x - 1 where x ∈ Nat - {0}: can be 0 when x = 1, so Nat - {0} fails.
#[test]
fn diff_range_pred_counterexample() {
    counterexample(
        "
bad : Nat - {0} -> Nat - {0}
bad(x) = x - 1
",
    );
}

// ── Symmetric difference (^) in domain ───────────────────────────────────────

// Nat ^ {0} = NatPos; arithmetic x + 1 ≥ 2, NatPos proved.
#[test]
fn sym_diff_domain_add_one_proved() {
    proved(
        "
succ : Nat ^ {0} -> NatPos
succ(x) = x + 1
",
    );
}

// x ∈ Nat ^ {0} = NatPos, so x - 1 ≥ 0 ∈ Nat.
#[test]
fn sym_diff_domain_pred_to_nat_proved() {
    proved(
        "
pred : Nat ^ {0} -> Nat
pred(x) = x - 1
",
    );
}

// x - 1 = 0 when x = 1; NatPos range fails.
#[test]
fn sym_diff_domain_pred_to_natpos_counterexample() {
    counterexample(
        "
pred : Nat ^ {0} -> NatPos
pred(x) = x - 1
",
    );
}

// x * 2 where x ∈ NatPos gives ≥ 2 > 0; NatPos range holds.
#[test]
fn sym_diff_domain_double_proved() {
    proved(
        "
double : Nat ^ {0} -> NatPos
double(x) = x * 2
",
    );
}

// ── Symmetric difference (^) in range ────────────────────────────────────────

// NatPos = Nat ^ {0}; returning a NatPos value is proved.
#[test]
fn sym_diff_range_natpos_proved() {
    proved(
        "
f : NatPos -> Nat ^ {0}
f(x) = x
",
    );
}

// 0 ∈ Nat but 0 ∉ Nat ^ {0}; identity from Nat fails.
#[test]
fn sym_diff_range_nat_counterexample() {
    counterexample(
        "
bad : Nat -> Nat ^ {0}
bad(x) = x
",
    );
}

// x + 1 from NatPos gives ≥ 2, still in NatPos = Nat ^ {0}.
#[test]
fn sym_diff_range_succ_proved() {
    proved(
        "
succ : NatPos -> Nat ^ {0}
succ(x) = x + 1
",
    );
}

// Returning a Nat ^ {0} value back into Nat ^ {0}: identity proved.
#[test]
fn sym_diff_range_identity_proved() {
    proved(
        "
f : Nat ^ {0} -> Nat ^ {0}
f(x) = x
",
    );
}

// Returning 0 from any domain into Nat ^ {0} always fails.
#[test]
fn sym_diff_range_constant_zero_counterexample() {
    counterexample(
        "
bad : NatPos -> Nat ^ {0}
bad(x) = 0
",
    );
}

// ── Disjoint union (+) in domain ─────────────────────────────────────────────

// x : {0} + NatPos = Nat; x + 1 ≥ 1 ∈ NatPos.
#[test]
fn disjoint_domain_add_one_to_natpos_proved() {
    proved(
        "
succ : {0} + NatPos -> NatPos
succ(x) = x + 1
",
    );
}

// Two args: x ∈ {0} + NatPos = Nat, y ∈ NatPos; x + y ≥ 1.
#[test]
fn disjoint_domain_two_arg_sum_proved() {
    proved(
        "
f : ({0} + NatPos) * NatPos -> NatPos
f(x, y) = x + y
",
    );
}

// ── Disjoint union (+) in range ───────────────────────────────────────────────

// 0 ∈ {0}; satisfies {0} + NatPos range.
#[test]
fn disjoint_range_zero_proved() {
    proved(
        "
f : -> {0} + NatPos
f() = 0
",
    );
}

// NatPos values satisfy the NatPos arm of {0} + NatPos.
#[test]
fn disjoint_range_natpos_proved() {
    proved(
        "
f : NatPos -> {0} + NatPos
f(x) = x
",
    );
}

// -1 is not in {0} + NatPos.
#[test]
fn disjoint_range_neg_one_counterexample() {
    counterexample(
        "
f : -> {0} + NatPos
f() = -1
",
    );
}

// Plain Int input — negative values break {0} + NatPos range.
#[test]
fn disjoint_range_int_counterexample() {
    counterexample(
        "
bad : Int -> {0} + NatPos
bad(x) = x
",
    );
}

// ── Disjoint union (+) nested inside a Kleene star (X*) ──────────────────────
//
// `validate_disjoint_unions` recurses into `DisjointUnion`/`SetDifference`/
// `CartesianProduct`/`BinOp`/`Call` but used to have no case for `KleeneStar`,
// so a `+` inside `(A + B)*` fell through the wildcard `_ => None` arm and
// skipped the disjointness check entirely — `({0} + Nat)*`, whose arms
// plainly overlap on 0, used to falsely report Proved instead of the
// spurious-but-caught-elsewhere "not disjoint" Counterexample.

// {0} and NatPos are genuinely disjoint — the Kleene-star case must still
// let a correct disjoint union through.
#[test]
fn disjoint_union_in_kleene_star_domain_proved() {
    proved(
        "
f : ({0} + NatPos)* -> Nat
f(xs) = 0
",
    );
}

// {0} and Nat overlap on 0 — must be caught even nested inside `X*`.
#[test]
fn disjoint_union_in_kleene_star_domain_not_disjoint_counterexample() {
    counterexample(
        "
f : ({0} + Nat)* -> Nat
f(xs) = 0
",
    );
}

// Same check in range position.
#[test]
fn disjoint_union_in_kleene_star_range_not_disjoint_counterexample() {
    counterexample(
        "
f : -> ({0} + Nat)*
f() = []
",
    );
}

// ── Cross-operator combinations ───────────────────────────────────────────────

// (Nat - {0}) | {0} = Nat; identity into Nat proved.
#[test]
fn cross_diff_or_zero_covers_nat_proved() {
    proved(
        "
f : (Nat - {0}) | {0} -> Nat
f(x) = x
",
    );
}

// ── Cross-sort symmetric difference (^) ──────────────────────────────────────
// When the LHS and RHS of `^` have different CVC5 sorts, `set_sort` builds one
// of two things depending on whether the sides can share a representable value:
//
//   1. One side is a Kleene-star `X*` whose element sort matches the other
//      side's natural sort (scalar) or all of its tuple components (product):
//      the existing sequence-unification bridges (`lift_sequence_into_atomic`
//      in membership.rs) already make membership correct once `t` is declared
//      with the sequence's CVC5 sort — no wrapper datatype needed.
//      e.g. `Nat* ^ Int`, `(Nat * Nat) ^ Int`.
//
//   2. Otherwise the two sides can never share a representable value under any
//      existing coercion (Bool vs Int-family, tuple vs scalar with no
//      Kleene-star involved, …) — they are provably disjoint, so `A ^ B`
//      literally equals `A ∪ B` (XOR of disjoint sets = OR). This reuses the
//      same cross-kind tagged datatype as `|`.
//      e.g. `Bool ^ Nat`.
//
// Sequence unification is a *coercion* that applies to bare scalars checked
// against a Kleene-star set, not to bracket-literal values: `[n]` elaborates
// to a concrete fixed-length tuple/vector term (checked against `Nat*` via
// per-child projection) and is never a member of a plain scalar set like `Int`
// (there's no established tuple-to-scalar bridge outside of Kleene-star
// targets) — so e.g. `[1, 2]` is in `Nat* ^ Int` only via its `Nat*` arm.
// The Int arm only actually contributes *new* (non-Nat*) values through a bare
// scalar *parameter*, which CVC5 represents symbolically and which the
// scalar-coercion rule (`t ∈ X* ⟺ t ∈ X`) applies to directly: a scalar `x` is
// `∈ Nat* ^ Int` iff exactly one of (`x ∈ Nat`, `x ∈ Int`) holds — `x ∈ Int` is
// always true, so this reduces to `x ∉ Nat`, i.e. `x < 0`. (An earlier,
// pre-implementation draft of these tests assumed "Int ⊆ Nat*" unconditionally
// and derived "sequences of length ≠ 1" — that's wrong on both counts, as
// corrected here against the actual solver output.)

// [1, 2]: a genuine 2-element Nat* sequence; never an Int member (no
// tuple-to-scalar bridge), so it's in the symdiff via its Nat* arm.
#[test]
fn cross_sort_sym_diff_kleene_int_len2_proved() {
    proved(
        "
f : -> Nat* ^ Int
f() = [1, 2]
",
    );
}

// A negative scalar is never in Nat* (even via coercion, since it's not in
// Nat) but always in Int — in the symdiff via its Int arm.
#[test]
fn cross_sort_sym_diff_kleene_int_negative_scalar_proved() {
    proved(
        "
f : Int - Nat -> Nat* ^ Int
f(x) = x
",
    );
}

// A non-negative scalar is in *both* Nat* (via coercion) and Int, so it's
// excluded from the symmetric difference.
#[test]
fn cross_sort_sym_diff_kleene_int_nonneg_scalar_counterexample() {
    counterexample(
        "
bad : Nat -> Nat* ^ Int
bad(x) = x
",
    );
}

// Subtracting `Int` removes every length-1 sequence (the only ones with an
// `Int` interpretation) and `{[]}` removes the length-0 case, leaving exactly
// "length ≥ 2 sequences of naturals" — safe for xs[0] + xs[1].
#[test]
fn cross_sort_sym_diff_kleene_minus_scalar_proved() {
    proved(
        "
h : (Nat* ^ Int) - Int - {[]} -> Nat
h(xs) = xs[0] + xs[1]
",
    );
}

// Once length-1 sequences are excluded the same way, every remaining member is
// a genuine (possibly empty) sequence of naturals — identity into Nat* holds.
#[test]
fn cross_sort_sym_diff_kleene_scalar_identity_proved() {
    proved(
        "
f : (Nat* ^ Int) - Int -> Nat*
f(xs) = xs
",
    );
}

// (2, 3): a genuine 2-tuple, never an `Int` (no tuple/scalar coercion exists
// outside of Kleene-star sequences) — so it's in the tagged-union symdiff via
// its (Nat * Nat) arm.
#[test]
fn cross_sort_sym_diff_tuple_scalar_tuple_arm_proved() {
    proved(
        "
f : -> (Nat * Nat) ^ Int
f() = (2, 3)
",
    );
}

// 5: a genuine scalar, in the symdiff via its Int arm.
#[test]
fn cross_sort_sym_diff_tuple_scalar_int_arm_proved() {
    proved(
        "
f : -> (Nat * Nat) ^ Int
f() = 5
",
    );
}

// (-1, 2): not in (Nat * Nat) (−1 ∉ Nat) and, being a tuple, never in Int
// either — in neither arm, so not a member of the symdiff.
#[test]
fn cross_sort_sym_diff_tuple_scalar_neither_arm_counterexample() {
    counterexample(
        "
bad : -> (Nat * Nat) ^ Int
bad() = (-1, 2)
",
    );
}

// Bool and Nat are genuinely disjoint (no implicit 0/1 conversion — see
// docs/design-decisions.md), so `Bool ^ Nat` is a tagged union exactly like
// `Bool | Nat`: a value is either a real Bool or a real Nat, never both.
// (An earlier draft of this test wrote `x + 1` on the union argument directly,
// which assumed the old, incorrect "Bool ⊆ Nat" identification — arithmetic on
// an un-narrowed union value isn't meaningful, so these test construction into
// the range instead, like the analogous `Nat* | Int` tests in vectors.rs.)

// true: a genuine Bool, in the symdiff via its Bool arm.
#[test]
fn cross_sort_sym_diff_bool_nat_bool_arm_proved() {
    proved(
        "
f : -> Bool ^ Nat
f() = true
",
    );
}

// 5: a genuine Nat, in the symdiff via its Nat arm.
#[test]
fn cross_sort_sym_diff_bool_nat_nat_arm_proved() {
    proved(
        "
f : -> Bool ^ Nat
f() = 5
",
    );
}

// -1: not a Bool, and not a Nat (Nat is non-negative) — in neither arm.
#[test]
fn cross_sort_sym_diff_bool_nat_neither_arm_counterexample() {
    counterexample(
        "
bad : -> Bool ^ Nat
bad() = -1
",
    );
}

// Nat ^ {0} and Nat - {0} are both NatPos; identity across operators proved.
#[test]
fn cross_sym_diff_to_set_diff_proved() {
    proved(
        "
f : Nat ^ {0} -> Nat - {0}
f(x) = x
",
    );
}

// Reverse direction: Nat - {0} into Nat ^ {0}.
#[test]
fn cross_set_diff_to_sym_diff_proved() {
    proved(
        "
f : Nat - {0} -> Nat ^ {0}
f(x) = x
",
    );
}

// Multi-operator domain: (Int - {0}) in both args makes division safe.
#[test]
fn cross_two_diff_args_safe_div_proved() {
    proved(
        "
f : (Int - {0}) * (Int - {0}) -> Int
f(x, y) = x / y
",
    );
}

// ── Cross-kind: Bool ∩ integer-valued sets ────────────────────────────────────
// Bool maps to CVC5's boolean sort; integer sets map to CVC5's integer sort.
// Both intersection (`&`) and union (`|`) are handled correctly today — see
// `cross_kind_bool_or_nat_*` below for the union cases.

// Bool & Nat: Bool = {0,1} ⊆ Nat so Bool & Nat = Bool.
// Identity back into Bool is proved.
#[test]
fn cross_kind_bool_and_nat_to_bool_proved() {
    proved(
        "
f : Bool & Nat -> Bool
f(x) = x
",
    );
}

// Bool & Nat = {0,1}; 0 (= false) is not in NatPos, so counterexample.
#[test]
fn cross_kind_bool_and_nat_to_natpos_counterexample() {
    counterexample(
        "
f : Bool & Nat -> NatPos
f(x) = x
",
    );
}

// Bool and Nat are disjoint (no implicit 0/1 conversion), so Bool & Nat is
// empty — a Bool-domain value can never satisfy it; counterexample.
#[test]
fn cross_kind_bool_to_bool_and_nat_counterexample() {
    counterexample(
        "
f : Bool -> Bool & Nat
f(x) = x
",
    );
}

// Bool & Int: Bool = {0,1} ⊆ Int, so Bool & Int = Bool.
#[test]
fn cross_kind_bool_and_int_to_bool_proved() {
    proved(
        "
f : Bool & Int -> Bool
f(x) = x
",
    );
}

// ── Cross-kind: Bool ∪ integer-valued sets ────────────────────────────────────
// Bool and Int are disjoint (no implicit 0/1 conversion), so `Bool | Nat` is a
// genuine cross-kind union — represented as a CVC5 tagged datatype, the same
// as `(Nat * Nat) | Nat`, not collapsed into plain integer sort.

// A Nat value is wrapped into the Nat arm of the tagged union; proved.
#[test]
fn cross_kind_bool_or_nat_range_from_nat_proved() {
    proved(
        "
f : Nat -> Bool | Nat
f(x) = x
",
    );
}

// A Bool value is wrapped into the Bool arm of the tagged union; proved.
#[test]
fn cross_kind_bool_or_nat_range_from_bool_proved() {
    proved(
        "
f : Bool -> Bool | Nat
f(x) = x
",
    );
}

// A `Bool | Nat`-domain value is a tagged union, not a plain boolean — using
// it directly as an `if` condition needs narrowing that doesn't exist yet, so
// this is rejected at elaboration rather than silently treating the tag/payload
// as a boolean (which is exactly the "Bool ⊆ Int" bug this union sort fixes).
#[test]
fn cross_kind_bool_or_nat_domain_used_as_condition_rejected() {
    rejected(
        "
f : Bool | Nat -> Nat
f(x) = if x then 1 else 0
",
    );
}

// A Nat value like 2 is in Bool | Nat but not in Bool; counterexample.
#[test]
fn cross_kind_bool_or_nat_to_bool_counterexample() {
    counterexample(
        "
bad : Bool | Nat -> Bool
bad(x) = x
",
    );
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
    proved(
        "
f : Nat -> (Nat * Nat) | Nat
f(x) = (x, x)
",
    );
}

// ── Distinct sets in unions ───────────────────────────────────────────────────
// `distinct` sets have an uninterpreted membership predicate (`is_Litre : Int -> Bool`).
// The solver does not automatically know that Litre values satisfy their basis (Nat) —
// it only learns this when constructors or destructors are used.  So `Litre | Nat`
// as a domain is strictly broader than `Nat`: Litre values may fall outside Nat.

// Returning a Litre value into a Litre | Nat range: is_Litre(x) satisfies the Litre arm.
#[test]
fn distinct_in_union_range_proved() {
    proved(
        "
Litre = distinct Nat
f : Litre -> Litre | Nat
f(x) = x
",
    );
}

// Returning a NatPos value into a Litre | Nat range: NatPos ⊆ Nat satisfies the Nat arm.
#[test]
fn scalar_in_distinct_union_range_proved() {
    proved(
        "
Litre = distinct Nat
f : NatPos -> Litre | Nat
f(x) = x
",
    );
}

// Identity from Litre | Nat into Nat: a Litre value is not in Nat so this should
// be a counterexample.
#[test]
fn distinct_union_to_nat_counterexample() {
    counterexample(
        "
Litre = distinct Nat
f : Litre | Nat -> Nat
f(x) = x
",
    );
}

// Two distinct sets based on Nat: a Metre value satisfies the Metre arm of Metre | Litre.
#[test]
fn two_distinct_sets_in_union_proved() {
    proved(
        "
Metre = distinct Nat
Litre = distinct Nat
f : Metre -> Metre | Litre
f(x) = x
",
    );
}

// Metre and Litre are independent uninterpreted predicates; a Metre value need not
// satisfy is_Litre.  Identity from Metre into Litre gives a counterexample.
#[test]
fn two_distinct_sets_cross_arm_counterexample() {
    counterexample(
        "
Metre = distinct Nat
Litre = distinct Nat
f : Metre -> Litre
f(x) = x
",
    );
}

// Constructor wraps a NatPos into Litre, satisfying the Litre arm of Litre | NatPos.
#[test]
fn distinct_constructor_in_union_range_proved() {
    proved(
        "
Litre = distinct Nat
f : NatPos -> Litre | NatPos
f(x) = litre(x)
",
    );
}

// ── Cross-kind: tuple | scalar in domain (needs tagged-union CVC5 sort) ───────
// Creating a parameter variable from a domain like `(Nat * Nat) | Nat` requires a
// single CVC5 sort that can represent both a tuple and an integer — which does not
// These now use the CVC5 algebraic datatype encoding added in Step 6.

// Constant body: should be proved regardless of the cross-kind domain.
#[test]
fn cross_kind_tuple_or_nat_const_proved() {
    proved(
        "
f : (Nat * Nat) | Nat -> Nat
f(x) = 1
",
    );
}

// Identity into Nat should be a counterexample: if x is a tuple, x ∉ Nat.
#[test]
fn cross_kind_tuple_or_nat_domain_identity_counterexample() {
    counterexample(
        "
f : (Nat * Nat) | Nat -> Nat
f(x) = x
",
    );
}

// Arms reversed: Nat | (Nat * Nat) with constant body.
#[test]
fn cross_kind_nat_or_tuple_domain_const_proved() {
    proved(
        "
f : Nat | (Nat * Nat) -> Nat
f(x) = 1
",
    );
}

// Bool | tuple cross-kind domain.
#[test]
fn cross_kind_bool_or_tuple_domain_const_proved() {
    proved(
        "
f : Bool | (Nat * Nat) -> Nat
f(x) = 1
",
    );
}

// ── Kind mismatch: body and range have incompatible kinds ─────────────────────
// Cantor has no type-checking phase, so kind-mismatched programs reach the solver.
// The solver gives a spurious counterexample because
// `membership_constraint(tuple_body, Nat)` returns `Constrained(false)` — a tuple
// can never be an integer — making the range obligation trivially SAT for any model.
// The codegen would catch this mismatch later; the solver does not diagnose it.
#[test]
fn kind_mismatch_tuple_body_scalar_range_counterexample() {
    counterexample(
        "
f : Nat -> Nat
f(x) = (x, x)
",
    );
}
