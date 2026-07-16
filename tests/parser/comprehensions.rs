use cantor::ast::{BinOp, ExprKind};
use cantor::span::Symbol;

use super::helpers::*;

// ── Set comprehensions ────────────────────────────────────────────────────────

#[test]
fn comprehension_no_filter() {
    let kind = parse("{x * 2 for x in {1, 3, 5}}");
    let ExprKind::Comprehension {
        output,
        var,
        source,
        filter,
    } = kind
    else {
        panic!("expected Comprehension, got {kind:?}");
    };
    assert!(matches!(
        output.kind,
        ExprKind::BinOp { op: BinOp::Mul, .. }
    ));
    assert_eq!(var, Symbol::new("x"));
    assert!(matches!(source.kind, ExprKind::SetLit(_)));
    assert!(filter.is_none());
}

#[test]
fn comprehension_with_filter() {
    let kind = parse("{x for x in {1, 2, 3, 4, 5} if x > 2}");
    let ExprKind::Comprehension {
        output,
        var,
        source,
        filter,
    } = kind
    else {
        panic!("expected Comprehension, got {kind:?}");
    };
    assert!(matches!(output.kind, ExprKind::Var(s) if s.0 == "x"));
    assert_eq!(var, Symbol::new("x"));
    assert!(matches!(source.kind, ExprKind::SetLit(_)));
    assert!(filter.is_some());
    assert!(matches!(
        filter.unwrap().kind,
        ExprKind::BinOp { op: BinOp::Gt, .. }
    ));
}

#[test]
fn comprehension_named_source() {
    // Source can be a named set (like Nat) — generative set at compile time.
    let kind = parse("{x for x in Nat if x > 0}");
    let ExprKind::Comprehension { source, .. } = kind else {
        panic!("expected Comprehension");
    };
    assert!(matches!(source.kind, ExprKind::Var(s) if s.0 == "Nat"));
}

#[test]
fn comprehension_vs_set_literal_disambiguation() {
    // {1, 2, 3} is a set literal, not a comprehension.
    assert!(matches!(parse("{1, 2, 3}"), ExprKind::SetLit(_)));
    // {x * 2 for x in S} is a comprehension.
    assert!(matches!(
        parse("{x * 2 for x in {1}}"),
        ExprKind::Comprehension { .. }
    ));
}

#[test]
fn empty_set_literal_still_works() {
    assert!(matches!(parse("{}"), ExprKind::SetLit(elems) if elems.is_empty()));
}

#[test]
fn comprehension_display_round_trips() {
    use cantor::ast::Expr;
    let comp = Expr::comprehension(
        Expr::binop(BinOp::Mul, Expr::var("x"), Expr::int(2)),
        "x",
        Expr::set_lit(vec![Expr::int(1), Expr::int(3)]),
        None,
    );
    assert_eq!(format!("{comp}"), "{x * 2 for x in {1, 3}}");
}

#[test]
fn comprehension_display_with_filter() {
    use cantor::ast::Expr;
    let comp = Expr::comprehension(
        Expr::var("x"),
        "x",
        Expr::set_lit(vec![Expr::int(1), Expr::int(2), Expr::int(3)]),
        Some(Expr::binop(BinOp::Gt, Expr::var("x"), Expr::int(1))),
    );
    assert_eq!(format!("{comp}"), "{x for x in {1, 2, 3} if x > 1}");
}
