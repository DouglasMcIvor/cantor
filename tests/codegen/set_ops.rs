use super::helpers::*;

// ── Disjoint union (`+`) in domain ───────────────────────────────────────────

#[test]
fn disjoint_union_domain_identity() {
    // x : {0} + NatPos — just return the value unchanged.
    assert_eq!(jit_src_one_arg("main : {0} + NatPos -> Nat\nmain(x) = x", 0),  0);
    assert_eq!(jit_src_one_arg("main : {0} + NatPos -> Nat\nmain(x) = x", 5),  5);
    assert_eq!(jit_src_one_arg("main : {0} + NatPos -> Nat\nmain(x) = x", 1),  1);
}

#[test]
fn disjoint_union_domain_arithmetic() {
    // x : {0} + NatPos — arithmetic still works on the payload.
    assert_eq!(jit_src_one_arg("main : {0} + NatPos -> Int\nmain(x) = x + 1", 0), 1);
    assert_eq!(jit_src_one_arg("main : {0} + NatPos -> Int\nmain(x) = x + 1", 9), 10);
}

#[test]
fn disjoint_union_domain_membership_in_body() {
    // Runtime check `x in {0}` on a disjoint-union-typed parameter.
    let src = "
main : {0} + NatPos -> Bool
main(x) = if x in {0} then true else false
";
    assert_eq!(jit_src_one_arg(src, 0), 1);  // 0 ∈ {0}
    assert_eq!(jit_src_one_arg(src, 1), 0);  // 1 ∉ {0}
    assert_eq!(jit_src_one_arg(src, 7), 0);  // 7 ∉ {0}
}

// ── Disjoint union (`+`) in range ────────────────────────────────────────────

#[test]
fn disjoint_union_range_identity() {
    // Return a Nat value into a {0} + NatPos range.
    assert_eq!(jit_src_one_arg("main : Nat -> {0} + NatPos\nmain(x) = x", 0),  0);
    assert_eq!(jit_src_one_arg("main : Nat -> {0} + NatPos\nmain(x) = x", 3),  3);
}

// ── Symmetric difference (`^`) in domain ─────────────────────────────────────

#[test]
fn sym_diff_domain_identity() {
    // x : Nat ^ {0} = NatPos — body returns x which is > 0.
    assert_eq!(jit_src_one_arg("main : Nat ^ {0} -> NatPos\nmain(x) = x", 1),  1);
    assert_eq!(jit_src_one_arg("main : Nat ^ {0} -> NatPos\nmain(x) = x", 42), 42);
}

#[test]
fn sym_diff_domain_membership_in_body() {
    // x : Nat ^ {0} — check x in {0} (always false for NatPos elements).
    let src = "
main : Nat ^ {0} -> Bool
main(x) = if x in {0} then true else false
";
    assert_eq!(jit_src_one_arg(src, 1),  0); // 1 ∉ {0}
    assert_eq!(jit_src_one_arg(src, 5),  0); // 5 ∉ {0}
}

// ── Symmetric difference (`^`) in range ──────────────────────────────────────

#[test]
fn sym_diff_range_identity() {
    // f : NatPos -> Nat ^ {0}; f(x) = x — returns NatPos which = Nat ^ {0}.
    assert_eq!(jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x", 1),  1);
    assert_eq!(jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x", 10), 10);
}

#[test]
fn sym_diff_range_arithmetic() {
    // f : NatPos -> Nat ^ {0}; x + 1 ≥ 2, still a valid NatPos / Nat ^ {0} value.
    assert_eq!(jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x + 1", 1),  2);
    assert_eq!(jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x + 1", 9), 10);
}

// ── Union (`|`) in domain ─────────────────────────────────────────────────────

#[test]
fn union_domain_int8_range_identity() {
    // Value in Int8 range passed to Int8 | Int16 domain; returned as Int.
    assert_eq!(jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", 100), 100);
    assert_eq!(jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", -50), -50);
}

#[test]
fn union_domain_int16_range_identity() {
    // Value in Int16 but outside Int8; identity still works.
    assert_eq!(jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", 500),  500);
    assert_eq!(jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", -500), -500);
}

#[test]
fn union_domain_arithmetic() {
    assert_eq!(jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x * 2", 50),  100);
    assert_eq!(jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x * 2", -10), -20);
}

#[test]
fn union_domain_membership_in_body() {
    // Check which arm x belongs to: Int8 is -128..127, Int16 extends beyond that.
    let src = "
main : Int8 | Int16 -> Int
main(x) = if x in Int8 then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 50),  1); // 50 ∈ Int8
    assert_eq!(jit_src_one_arg(src, 500), 0); // 500 ∉ Int8
}

#[test]
fn union_domain_nat_or_neg_membership() {
    // {0} | NatPos = Nat. Check membership in each sub-set from the body.
    let src = "
main : {0} | NatPos -> Int
main(x) = if x in {0} then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 0), 1); // 0 ∈ {0}
    assert_eq!(jit_src_one_arg(src, 5), 0); // 5 ∉ {0}
}

// ── Union (`|`) in range ──────────────────────────────────────────────────────

#[test]
fn union_range_from_int8() {
    assert_eq!(jit_src_one_arg("main : Int8 -> Int8 | Int16\nmain(x) = x", 42),  42);
    assert_eq!(jit_src_one_arg("main : Int8 -> Int8 | Int16\nmain(x) = x", -10), -10);
}

#[test]
fn union_range_from_int16() {
    assert_eq!(jit_src_one_arg("main : Int16 -> Int8 | Int16\nmain(x) = x", 1000),  1000);
    assert_eq!(jit_src_one_arg("main : Int16 -> Int8 | Int16\nmain(x) = x", -1000), -1000);
}

// ── Set difference (`-`) in domain ───────────────────────────────────────────

#[test]
fn diff_domain_int_minus_zero_identity() {
    // Int - {0} parameter; returned unchanged.
    assert_eq!(jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x",  7),  7);
    assert_eq!(jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x", -3), -3);
}

#[test]
fn diff_domain_int_minus_zero_arithmetic() {
    assert_eq!(jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x + x",  5),  10);
    assert_eq!(jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x + x", -4),  -8);
}

#[test]
fn diff_domain_nat_minus_zero_identity() {
    // Nat - {0} = NatPos; returned as Nat.
    assert_eq!(jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x", 5), 5);
    assert_eq!(jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x", 1), 1);
}

#[test]
fn diff_domain_pred() {
    // x - 1 where x ∈ Nat - {0}; result ≥ 0.
    assert_eq!(jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x - 1", 3), 2);
    assert_eq!(jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x - 1", 1), 0);
}

#[test]
fn diff_domain_membership_in_body() {
    // Nat - {0} parameter; x is always in NatPos.
    let src = "
main : Nat - {0} -> Int
main(x) = if x in NatPos then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 1), 1);
    assert_eq!(jit_src_one_arg(src, 5), 1);
}

// ── Set difference (`-`) in range ────────────────────────────────────────────

#[test]
fn diff_range_natpos_passthrough() {
    // NatPos -> Int - {0}; returning x unchanged.
    assert_eq!(jit_src_one_arg("main : NatPos -> Int - {0}\nmain(x) = x", 5), 5);
    assert_eq!(jit_src_one_arg("main : NatPos -> Int - {0}\nmain(x) = x", 1), 1);
}

#[test]
fn diff_range_nat_minus_zero_passthrough() {
    // Nat - {0} -> Nat - {0}; identity.
    assert_eq!(jit_src_one_arg("main : Nat - {0} -> Nat - {0}\nmain(x) = x", 3), 3);
    assert_eq!(jit_src_one_arg("main : Nat - {0} -> Nat - {0}\nmain(x) = x", 7), 7);
}

// ── Cross-kind: Bool mixed with integer sets ──────────────────────────────────
// Bool values are i1 in LLVM but currently passed/returned as i64 (0 or 1).
// The tests below pass bool-encoded integers (0=false, 1=true) through unions
// that span both the Bool and integer kinds.  Today the codegen falls back to
// i64 for everything, so these may pass "accidentally"; they become the baseline
// to regression-test once proper tagged-union IR is emitted.

#[test]
fn cross_kind_bool_or_nat_domain_false_value() {
    // false (0) passed through Bool | Nat domain; identity returned as Int.
    assert_eq!(jit_src_one_arg("main : Bool | Nat -> Int\nmain(x) = x", 0), 0);
}

#[test]
fn cross_kind_bool_or_nat_domain_true_value() {
    // true (1) passed through Bool | Nat domain.
    assert_eq!(jit_src_one_arg("main : Bool | Nat -> Int\nmain(x) = x", 1), 1);
}

#[test]
fn cross_kind_bool_or_nat_domain_nat_value() {
    // A plain Nat value (not a Bool) passed through Bool | Nat domain.
    assert_eq!(jit_src_one_arg("main : Bool | Nat -> Int\nmain(x) = x", 5), 5);
}

#[test]
fn cross_kind_bool_or_nat_body_membership() {
    // Membership check distinguishes Bool arm from Nat-only arm.
    // 0 and 1 are in Bool; 2, 3, … are in Nat but not Bool.
    let src = "
main : Bool | Nat -> Int
main(x) = if x in Bool then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 0), 1); // false ∈ Bool
    assert_eq!(jit_src_one_arg(src, 1), 1); // true  ∈ Bool
    assert_eq!(jit_src_one_arg(src, 2), 0); // 2 ∉ Bool
    assert_eq!(jit_src_one_arg(src, 5), 0); // 5 ∉ Bool
}

#[test]
fn cross_kind_bool_to_bool_or_nat_range() {
    // Returning a Bool value (0 or 1) into a Bool | Nat range.
    assert_eq!(jit_src_one_arg("main : Bool -> Bool | Nat\nmain(x) = x", 0), 0);
    assert_eq!(jit_src_one_arg("main : Bool -> Bool | Nat\nmain(x) = x", 1), 1);
}

#[test]
fn cross_kind_nat_to_bool_or_nat_range() {
    // Returning a Nat value into a Bool | Nat range.
    assert_eq!(jit_src_one_arg("main : Nat -> Bool | Nat\nmain(x) = x", 3), 3);
    assert_eq!(jit_src_one_arg("main : Nat -> Bool | Nat\nmain(x) = x", 0), 0);
}

// ── Cross-kind: tuples mixed with scalar sets ─────────────────────────────────
// A * B is an {i64, i64} struct in LLVM IR; mixing it with Bool or Nat in a
// union requires a tagged-union representation ({i1 tag, payload}).  The
// existing codegen has no such representation, so these tests are #[ignore]
// until proper tagged-union IR emission is implemented.


#[test]
fn cross_kind_bool_or_tuple_bool_arm() {
    // Pass a Bool value (arm 0) through a Bool | (Nat * Nat) domain; body ignores x.
    assert_eq!(
        jit_src_one_arg("main : Bool | (Nat * Nat) -> Int\nmain(x) = 1", 0),
        1,
    );
}

#[test]
fn cross_kind_tuple_or_nat_nat_arm() {
    // Pass a Nat value (arm 1) through a (Nat * Nat) | Nat domain; body ignores x.
    assert_eq!(
        jit_src_one_arg("main : (Nat * Nat) | Nat -> Int\nmain(x) = 1", 7),
        1,
    );
}

// ── Cross-kind: tagged-union return values (Steps 4–5) ───────────────────────

#[test]
fn cross_kind_return_nat_arm_from_tagged_union() {
    // f returns x as the Nat arm of (Nat * Nat) | Nat; main checks membership.
    let src = "
f : Nat -> (Nat * Nat) | Nat
f(x) = x

main : Nat -> Int
main(x) = if f(x) in Nat then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 5), 1);
    assert_eq!(jit_src_one_arg(src, 0), 1);
}

#[test]
fn cross_kind_return_tuple_arm_from_tagged_union() {
    // f returns (x, x+1) as the tuple arm of (Nat * Nat) | Nat; main checks membership.
    let src = "
f : Nat -> (Nat * Nat) | Nat
f(x) = (x, x + 1)

main : Nat -> Int
main(x) = if f(x) in (Nat * Nat) then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 5), 1);
    assert_eq!(jit_src_one_arg(src, 0), 1);
}

#[test]
fn cross_kind_if_else_picks_correct_arm() {
    // f chooses the tuple arm when x > 0 and the Nat arm when x == 0.
    let src = "
f : Nat -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, x) else x

main : Nat -> Int
main(x) = if f(x) in (Nat * Nat) then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 5), 1); // x > 0 → tuple arm
    assert_eq!(jit_src_one_arg(src, 0), 0); // x == 0 → scalar arm
}

#[test]
#[ignore]
// compile_if's `needs_tagged_union` path only handles the two-arm case where
// neither branch is already a TaggedUnion.  Here the outer if has
//   then : TaggedUnion([Tuple([Int,Int]), Int])  (from the inner if)
//   else : Bool
// which hits the `else` fallthrough instead of merging into a 3-arm
// TaggedUnion([Tuple, Int, Bool]).  Fix: detect when one branch is a
// TaggedUnion and the other is a different kind; flatten the arms and wrap
// both values into the combined TaggedUnion before the phi merge.
fn cross_kind_three_arm_union_if_else() {
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x > 2 then (if x > 5 then (x, x) else x) else false

main : Nat -> Int
main(x) = if f(x) in (Nat * Nat) then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 1); // x > 5  → tuple arm
    assert_eq!(jit_src_one_arg(src, 4), 0); // 2 < x ≤ 5 → Nat arm
    assert_eq!(jit_src_one_arg(src, 1), 0); // x ≤ 2  → Bool arm
}

#[test]
fn cross_kind_tuple_arm_domain_membership_check() {
    // Check which arm of a (Nat * Nat) | Nat value was passed by inspecting the tag.
    // A scalar passed as jit_src_one_arg occupies the Nat arm (tag = 1), so the
    // membership check `x in (Nat * Nat)` (arm 0) should return false → 0.
    let src = "
main : (Nat * Nat) | Nat -> Int
main(x) = if x in (Nat * Nat) then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 5), 0);
}
