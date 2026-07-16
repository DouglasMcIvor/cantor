use cantor::ast::{BinOp, ExprKind, Item};
use cantor::parser::{parse_file, parse_set_expr};

use super::helpers::*;

// ── Repeated products `X * N` ─────────────────────────────────────────────────
// `Int * 3` desugars at parse time into `(Int * Int) * Int` (left-assoc).
// Desugaring happens in parse_set_expr (set positions only — in value position
// `x * 3` remains arithmetic multiplication).

#[test]
fn parse_repeated_product_two() {
    // X * 2  →  Mul(X, X) — two Var nodes, not Mul(X, IntLit(2)).
    let ExprKind::BinOp { op, lhs, rhs } = parse_set("Int * 2") else {
        panic!()
    };
    assert_eq!(op, BinOp::Mul);
    assert!(
        matches!(lhs.kind, ExprKind::Var(ref s) if s.0 == "Int"),
        "lhs should be Int"
    );
    assert!(
        matches!(rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"),
        "rhs should be Int (desugared copy), not IntLit(2)"
    );
}

#[test]
fn parse_repeated_product_three() {
    // X * 3  →  Mul(Mul(X, X), X)  — left-associated tree of Var nodes.
    let ExprKind::BinOp {
        op: outer_op,
        lhs: outer_lhs,
        rhs: outer_rhs,
    } = parse_set("Int * 3")
    else {
        panic!()
    };
    assert_eq!(outer_op, BinOp::Mul);
    assert!(
        matches!(outer_rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"),
        "outer rhs should be Int Var"
    );
    let ExprKind::BinOp {
        op: inner_op,
        lhs: inner_lhs,
        rhs: inner_rhs,
    } = outer_lhs.kind
    else {
        panic!("lhs of outer Mul should itself be a Mul")
    };
    assert_eq!(inner_op, BinOp::Mul);
    assert!(matches!(inner_lhs.kind, ExprKind::Var(ref s) if s.0 == "Int"));
    assert!(matches!(inner_rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"));
}

#[test]
fn parse_repeated_product_one_is_identity() {
    // X * 1  →  bare X (no Mul wrapper).
    let kind = parse_set("Nat * 1");
    assert!(
        matches!(kind, ExprKind::Var(ref s) if s.0 == "Nat"),
        "Nat * 1 should desugar to bare Nat; got {kind:?}"
    );
}

// ── Kleene-star set expressions `X*` ─────────────────────────────────────────

#[test]
fn parse_kleene_star_simple() {
    let kind = parse_set_expr("Nat*").unwrap().kind;
    assert!(
        matches!(kind, ExprKind::KleeneStar(ref inner) if matches!(inner.kind, ExprKind::Var(ref s) if s.0 == "Nat")),
        "Nat* should parse as KleeneStar(Var(Nat)); got {kind:?}"
    );
}

#[test]
fn parse_kleene_star_parenthesised_set() {
    let kind = parse_set_expr("(Nat - {0})*").unwrap().kind;
    assert!(
        matches!(kind, ExprKind::KleeneStar(ref inner) if matches!(inner.kind, ExprKind::BinOp { op: BinOp::Sub, .. })),
        "(Nat - {{0}})* should parse as KleeneStar(BinOp(Sub, …)); got {kind:?}"
    );
}

#[test]
fn parse_kleene_star_in_function_sig() {
    let items = parse_file("f : Nat* -> Int*\nf(xs) = 0").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    let sig = &def.sigs[0];
    assert!(
        matches!(
            sig.domain.as_ref().map(|d| &d.kind),
            Some(ExprKind::KleeneStar(_))
        ),
        "domain should be KleeneStar; got {:?}",
        sig.domain
    );
    assert!(
        matches!(&sig.range.kind, ExprKind::KleeneStar(_)),
        "range should be KleeneStar; got {:?}",
        sig.range.kind
    );
}

#[test]
fn parse_kleene_star_does_not_consume_mul_rhs() {
    // `Nat * Int` is multiplication (Int starts an expression), not Kleene star.
    let kind = parse_set_expr("Nat * Int").unwrap().kind;
    assert!(
        matches!(kind, ExprKind::BinOp { op: BinOp::Mul, .. }),
        "Nat * Int should parse as Mul, not KleeneStar; got {kind:?}"
    );
}
