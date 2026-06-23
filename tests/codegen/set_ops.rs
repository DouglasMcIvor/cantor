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
