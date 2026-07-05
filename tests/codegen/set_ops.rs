use super::helpers::*;

// ── Disjoint union (`+`) in domain ───────────────────────────────────────────

#[test]
fn disjoint_union_domain_identity() {
    // x : {0} + NatPos — a TaggedUnion({Int,Int}) param (`+` always tags, even
    // same-kind arms); narrowed back to a plain Nat by dropping the tag.
    assert_eq!(
        jit_src_tagged_domain("main : {0} + NatPos -> Nat\nmain(x) = x", 0, 0),
        0
    );
    assert_eq!(
        jit_src_tagged_domain("main : {0} + NatPos -> Nat\nmain(x) = x", 1, 5),
        5
    );
    assert_eq!(
        jit_src_tagged_domain("main : {0} + NatPos -> Nat\nmain(x) = x", 1, 1),
        1
    );
}

#[test]
fn disjoint_union_domain_arithmetic() {
    // x : {0} + NatPos — arithmetic still works on the narrowed payload.
    assert_eq!(
        jit_src_tagged_domain("main : {0} + NatPos -> Int\nmain(x) = x + 1", 0, 0),
        1
    );
    assert_eq!(
        jit_src_tagged_domain("main : {0} + NatPos -> Int\nmain(x) = x + 1", 1, 9),
        10
    );
}

#[test]
fn disjoint_union_domain_membership_in_body() {
    // Runtime check `x in {0}` on a disjoint-union-typed parameter.
    let src = "
main : {0} + NatPos -> Bool
main(x) = if x in {0} then true else false
";
    assert_eq!(jit_src_one_arg(src, 0), 1); // 0 ∈ {0}
    assert_eq!(jit_src_one_arg(src, 1), 0); // 1 ∉ {0}
    assert_eq!(jit_src_one_arg(src, 7), 0); // 7 ∉ {0}
}

// ── Disjoint union (`+`) in range ────────────────────────────────────────────

#[test]
fn disjoint_union_range_identity() {
    // Return a Nat value into a {0} + NatPos range. `{0}` and `NatPos` are both
    // Kind::Int, so codegen can't pick the tag by Kind alone — it must run a
    // real membership check (x in {0}) to disambiguate the arm at runtime.
    let src = "main : Nat -> {0} + NatPos\nmain(x) = x";
    assert_eq!(
        jit_src_tagged_range(src, 0),
        TaggedScalar { tag: 0, payload: 0 }
    ); // {0} arm
    assert_eq!(
        jit_src_tagged_range(src, 3),
        TaggedScalar { tag: 1, payload: 3 }
    ); // NatPos arm
}

// ── Symmetric difference (`^`) in domain ─────────────────────────────────────

#[test]
fn sym_diff_domain_identity() {
    // x : Nat ^ {0} = NatPos — body returns x which is > 0.
    assert_eq!(
        jit_src_one_arg("main : Nat ^ {0} -> NatPos\nmain(x) = x", 1),
        1
    );
    assert_eq!(
        jit_src_one_arg("main : Nat ^ {0} -> NatPos\nmain(x) = x", 42),
        42
    );
}

#[test]
fn sym_diff_domain_membership_in_body() {
    // x : Nat ^ {0} — check x in {0} (always false for NatPos elements).
    let src = "
main : Nat ^ {0} -> Bool
main(x) = if x in {0} then true else false
";
    assert_eq!(jit_src_one_arg(src, 1), 0); // 1 ∉ {0}
    assert_eq!(jit_src_one_arg(src, 5), 0); // 5 ∉ {0}
}

// ── Symmetric difference (`^`) in range ──────────────────────────────────────

#[test]
fn sym_diff_range_identity() {
    // f : NatPos -> Nat ^ {0}; f(x) = x — returns NatPos which = Nat ^ {0}.
    assert_eq!(
        jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x", 1),
        1
    );
    assert_eq!(
        jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x", 10),
        10
    );
}

#[test]
fn sym_diff_range_arithmetic() {
    // f : NatPos -> Nat ^ {0}; x + 1 ≥ 2, still a valid NatPos / Nat ^ {0} value.
    assert_eq!(
        jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x + 1", 1),
        2
    );
    assert_eq!(
        jit_src_one_arg("main : NatPos -> Nat ^ {0}\nmain(x) = x + 1", 9),
        10
    );
}

// ── Union (`|`) in domain ─────────────────────────────────────────────────────

#[test]
fn union_domain_int8_range_identity() {
    // Value in Int8 range passed to Int8 | Int16 domain; returned as Int.
    assert_eq!(
        jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", 100),
        100
    );
    assert_eq!(
        jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", -50),
        -50
    );
}

#[test]
fn union_domain_int16_range_identity() {
    // Value in Int16 but outside Int8; identity still works.
    assert_eq!(
        jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", 500),
        500
    );
    assert_eq!(
        jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x", -500),
        -500
    );
}

#[test]
fn union_domain_arithmetic() {
    assert_eq!(
        jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x * 2", 50),
        100
    );
    assert_eq!(
        jit_src_one_arg("main : Int8 | Int16 -> Int\nmain(x) = x * 2", -10),
        -20
    );
}

#[test]
fn union_domain_membership_in_body() {
    // Check which arm x belongs to: Int8 is -128..127, Int16 extends beyond that.
    let src = "
main : Int8 | Int16 -> Int
main(x) = if x in Int8 then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 50), 1); // 50 ∈ Int8
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
    assert_eq!(
        jit_src_one_arg("main : Int8 -> Int8 | Int16\nmain(x) = x", 42),
        42
    );
    assert_eq!(
        jit_src_one_arg("main : Int8 -> Int8 | Int16\nmain(x) = x", -10),
        -10
    );
}

#[test]
fn union_range_from_int16() {
    assert_eq!(
        jit_src_one_arg("main : Int16 -> Int8 | Int16\nmain(x) = x", 1000),
        1000
    );
    assert_eq!(
        jit_src_one_arg("main : Int16 -> Int8 | Int16\nmain(x) = x", -1000),
        -1000
    );
}

// ── Set difference (`-`) in domain ───────────────────────────────────────────

#[test]
fn diff_domain_int_minus_zero_identity() {
    // Int - {0} parameter; returned unchanged.
    assert_eq!(
        jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x", 7),
        7
    );
    assert_eq!(
        jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x", -3),
        -3
    );
}

#[test]
fn diff_domain_int_minus_zero_arithmetic() {
    assert_eq!(
        jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x + x", 5),
        10
    );
    assert_eq!(
        jit_src_one_arg("main : Int - {0} -> Int\nmain(x) = x + x", -4),
        -8
    );
}

#[test]
fn diff_domain_nat_minus_zero_identity() {
    // Nat - {0} = NatPos; returned as Nat.
    assert_eq!(
        jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x", 5),
        5
    );
    assert_eq!(
        jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x", 1),
        1
    );
}

#[test]
fn diff_domain_pred() {
    // x - 1 where x ∈ Nat - {0}; result ≥ 0.
    assert_eq!(
        jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x - 1", 3),
        2
    );
    assert_eq!(
        jit_src_one_arg("main : Nat - {0} -> Nat\nmain(x) = x - 1", 1),
        0
    );
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
    assert_eq!(
        jit_src_one_arg("main : NatPos -> Int - {0}\nmain(x) = x", 5),
        5
    );
    assert_eq!(
        jit_src_one_arg("main : NatPos -> Int - {0}\nmain(x) = x", 1),
        1
    );
}

#[test]
fn diff_range_nat_minus_zero_passthrough() {
    // Nat - {0} -> Nat - {0}; identity.
    assert_eq!(
        jit_src_one_arg("main : Nat - {0} -> Nat - {0}\nmain(x) = x", 3),
        3
    );
    assert_eq!(
        jit_src_one_arg("main : Nat - {0} -> Nat - {0}\nmain(x) = x", 7),
        7
    );
}

// ── Cross-kind: Bool mixed with integer sets ──────────────────────────────────
// Bool values are i1 in LLVM but currently passed/returned as i64 (0 or 1).
// The tests below pass bool-encoded integers (0=false, 1=true) through unions
// that span both the Bool and integer kinds.  Today the codegen falls back to
// i64 for everything, so these may pass "accidentally"; they become the baseline
// to regression-test once proper tagged-union IR is emitted.

// `Bool | Nat` compiles its parameter to a real `{i32 tag, i64 payload}`
// TaggedUnion struct — tag 0 is the Bool arm, tag 1 is the Nat arm (arm order
// follows source declaration order). Narrowing this union down to a plain
// `Int`/`Bool` return is unsound (Bool and Int/Nat are disjoint — see
// `cross_kind_bool_or_nat_domain_narrowed_to_bool_reports_compile_error`
// below) and the compiler now rejects it, so identity here has to keep the
// range as `Bool | Nat` too and round-trip through `jit_src_tagged_identity`.
#[test]
fn cross_kind_bool_or_nat_domain_false_value() {
    // false (tag 0, payload 0) passed through Bool | Nat identity.
    assert_eq!(
        jit_src_tagged_identity("main : Bool | Nat -> Bool | Nat\nmain(x) = x", 0, 0),
        TaggedScalar { tag: 0, payload: 0 }
    );
}

#[test]
fn cross_kind_bool_or_nat_domain_true_value() {
    // true (tag 0, payload 1) passed through Bool | Nat identity.
    assert_eq!(
        jit_src_tagged_identity("main : Bool | Nat -> Bool | Nat\nmain(x) = x", 0, 1),
        TaggedScalar { tag: 0, payload: 1 }
    );
}

#[test]
fn cross_kind_bool_or_nat_domain_nat_value() {
    // A plain Nat value (tag 1, not a Bool) passed through Bool | Nat identity.
    assert_eq!(
        jit_src_tagged_identity("main : Bool | Nat -> Bool | Nat\nmain(x) = x", 1, 5),
        TaggedScalar { tag: 1, payload: 5 }
    );
}

#[test]
fn cross_kind_bool_or_nat_body_membership() {
    // Membership check distinguishes Bool arm from Nat arm by tag, not value.
    let src = "
main : Bool | Nat -> Int
main(x) = if x in Bool then 1 else 0
";
    assert_eq!(jit_src_tagged_domain(src, 0, 0), 1); // false ∈ Bool
    assert_eq!(jit_src_tagged_domain(src, 0, 1), 1); // true  ∈ Bool
    assert_eq!(jit_src_tagged_domain(src, 1, 2), 0); // 2 ∉ Bool
    assert_eq!(jit_src_tagged_domain(src, 1, 5), 0); // 5 ∉ Bool
}

#[test]
fn cross_kind_bool_to_bool_or_nat_range() {
    // Returning a Bool value (0 or 1) into a Bool | Nat range; Bool is arm 0
    // (unambiguous — no other arm is Kind::Bool, so no membership check needed).
    let src = "main : Bool -> Bool | Nat\nmain(x) = x";
    assert_eq!(
        jit_src_tagged_range(src, 0),
        TaggedScalar { tag: 0, payload: 0 }
    );
    assert_eq!(
        jit_src_tagged_range(src, 1),
        TaggedScalar { tag: 0, payload: 1 }
    );
}

#[test]
fn cross_kind_nat_to_bool_or_nat_range() {
    // Returning a Nat value into a Bool | Nat range; Nat is arm 1.
    let src = "main : Nat -> Bool | Nat\nmain(x) = x";
    assert_eq!(
        jit_src_tagged_range(src, 3),
        TaggedScalar { tag: 1, payload: 3 }
    );
    assert_eq!(
        jit_src_tagged_range(src, 0),
        TaggedScalar { tag: 1, payload: 0 }
    );
}

// Narrowing a mixed-Kind TaggedUnion (Bool | Nat) down to a single arm's Kind
// is never sound — a Nat-arm payload is not a valid Bool (and vice versa), and
// there's no runtime tag check in this path, unlike `x in Bool`-style
// membership. This must be a compile error, not a silent payload truncation
// (regression test for narrow_tagged_union, which used to `trunc` the raw i64
// payload to i1 regardless of which arm it actually held).
#[test]
fn cross_kind_bool_or_nat_domain_narrowed_to_bool_reports_compile_error() {
    use cantor::{codegen::compile_file, parser::parse_file};
    use inkwell::context::Context;

    let src = "bad : Bool | Nat -> Bool\nbad(x) = x";
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let result = compile_file(&ctx, &items);
    assert!(result.is_err(), "expected a compile error, got {result:?}");
}

// ── Cross-kind: tuples mixed with scalar sets ─────────────────────────────────
// A * B is an {i64, i64} struct in LLVM IR; mixing it with Bool or Nat in a
// union requires a tagged-union representation ({i32 tag, i64 leaf...}).
// That representation exists and is exercised below (and further down, in
// the "tagged-union return values" and "three-arm union" sections).

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
fn cross_kind_three_arm_union_if_else() {
    // Outer if: then = TaggedUnion([Tuple, Int]) from inner if, else = Bool.
    // compile_if must extend the 2-arm TaggedUnion to 3-arm TaggedUnion([Tuple, Int, Bool]).
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
fn cross_kind_three_arm_union_else_is_tagged_union() {
    // Outer if: then = Bool, else = TaggedUnion([Tuple, Int]) from inner if.
    // compile_if must extend the 2-arm TaggedUnion to 3-arm TaggedUnion([Tuple, Int, Bool]).
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x <= 2 then false else (if x > 5 then (x, x) else x)

main : Nat -> Int
main(x) = if f(x) in (Nat * Nat) then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 1); // x > 5  → tuple arm
    assert_eq!(jit_src_one_arg(src, 4), 0); // 2 < x ≤ 5 → Nat arm
    assert_eq!(jit_src_one_arg(src, 1), 0); // x ≤ 2  → Bool arm
}

#[test]
fn cross_kind_three_arm_union_nat_arm_check() {
    // Verify tag 1 (Nat arm) is correctly identified in a 3-arm TaggedUnion.
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x > 2 then (if x > 5 then (x, x) else x) else false

main : Nat -> Int
main(x) = if f(x) in Nat then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 0); // tuple arm → not in Nat
    assert_eq!(jit_src_one_arg(src, 4), 1); // Nat arm   → in Nat
    assert_eq!(jit_src_one_arg(src, 1), 0); // Bool arm  → not in Nat
}

#[test]
fn cross_kind_three_arm_union_bool_arm_check() {
    // Verify tag 2 (Bool arm) is correctly identified in a 3-arm TaggedUnion.
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x > 2 then (if x > 5 then (x, x) else x) else false

main : Nat -> Int
main(x) = if f(x) in Bool then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 0); // tuple arm → not in Bool
    assert_eq!(jit_src_one_arg(src, 4), 0); // Nat arm   → not in Bool
    assert_eq!(jit_src_one_arg(src, 1), 1); // Bool arm  → in Bool
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

// ── Cross-kind: dual TaggedUnion merge ───────────────────────────────────────

// These tests exercise compile_if's dual-TaggedUnion path: both branches of the
// outer if already hold a TaggedUnion (produced by inner ifs), with different
// arm sets.  The merge deduplicates arms (then_arms first, then unique else_arms)
// and emits runtime `select` chains to remap the else branch's tag indices.
//
// f: outer if → then = TaggedUnion([Tuple, Int]), else = TaggedUnion([Bool, Tuple])
// merged = TaggedUnion([Tuple, Int, Bool])   (Tuple=0, Int=1, Bool=2)
// else tag remap: 0(Bool)→2, 1(Tuple)→0

#[test]
fn cross_kind_dual_tagged_union_merge_tuple_arm() {
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x > 3 then (if x > 5 then (x, x) else x) else (if x > 1 then false else (x, x + 1))

main : Nat -> Int
main(x) = if f(x) in (Nat * Nat) then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 1); // x>5  → then-path Tuple  (tag 0)
    assert_eq!(jit_src_one_arg(src, 4), 0); // x≤5  → then-path Int    (tag 1)
    assert_eq!(jit_src_one_arg(src, 2), 0); // x>1  → else-path Bool   (tag 2, remapped from 0)
    assert_eq!(jit_src_one_arg(src, 0), 1); // x≤1  → else-path Tuple  (tag 0, remapped from 1)
}

#[test]
fn cross_kind_dual_tagged_union_merge_nat_arm() {
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x > 3 then (if x > 5 then (x, x) else x) else (if x > 1 then false else (x, x + 1))

main : Nat -> Int
main(x) = if f(x) in Nat then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 0); // Tuple arm
    assert_eq!(jit_src_one_arg(src, 4), 1); // Int arm (tag 1)
    assert_eq!(jit_src_one_arg(src, 2), 0); // Bool arm
    assert_eq!(jit_src_one_arg(src, 0), 0); // Tuple arm (from else path)
}

#[test]
fn cross_kind_dual_tagged_union_merge_bool_arm() {
    let src = "
f : Nat -> (Nat * Nat) | Nat | Bool
f(x) = if x > 3 then (if x > 5 then (x, x) else x) else (if x > 1 then false else (x, x + 1))

main : Nat -> Int
main(x) = if f(x) in Bool then 1 else 0
";
    assert_eq!(jit_src_one_arg(src, 7), 0); // Tuple arm
    assert_eq!(jit_src_one_arg(src, 4), 0); // Int arm
    assert_eq!(jit_src_one_arg(src, 2), 1); // Bool arm (tag 2, remapped from 0)
    assert_eq!(jit_src_one_arg(src, 0), 0); // Tuple arm (from else path)
}

// ── `if` branches that cannot be merged fail loudly ─────────────────────────
//
// Neither branch is a Tuple or TaggedUnion here, so there's no coercion path
// codegen (or `kind::merge_if_branches`) can take — this used to fall through
// silently and build a phi from two different LLVM types (i64 vs i1); it now
// reports a compile error instead of producing invalid IR.

#[test]
fn cross_kind_int_vs_bool_branches_reports_compile_error() {
    use cantor::{codegen::compile_file, parser::parse_file};
    use inkwell::context::Context;

    let src = "main : Nat -> Int\nmain(x) = if x > 0 then 1 else true";
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let result = compile_file(&ctx, &items);
    assert!(result.is_err(), "expected a compile error, got {result:?}");
}
