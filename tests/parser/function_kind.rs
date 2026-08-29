//! Parsing for `Domain -> Range` as a nested function Kind (higher-order
//! functions, step 1 — parser only, see backlog.md). The bare top-level
//! `->` in a signature is unaffected (still consumed by `parse_item`); this
//! covers the new parenthesized-arrow grammar added to the `LParen` arm of
//! `parse_prefix`, which is the only place `->` may nest.

use cantor::ast::{BinOp, ExprKind, Item};
use cantor::parser::parse_file;

use super::helpers::*;

#[test]
fn parenthesized_arrow_parses_as_arrow_binop() {
    assert!(matches!(
        parse_set("(Int -> Int)"),
        ExprKind::BinOp {
            op: BinOp::Arrow,
            ..
        }
    ));
}

#[test]
fn parenthesized_arrow_lhs_rhs() {
    let ExprKind::BinOp {
        op: BinOp::Arrow,
        lhs,
        rhs,
    } = parse_set("(Int -> Nat)")
    else {
        panic!("expected Arrow BinOp");
    };
    assert!(matches!(lhs.kind, ExprKind::Var(ref s) if s.0 == "Int"));
    assert!(matches!(rhs.kind, ExprKind::Var(ref s) if s.0 == "Nat"));
}

#[test]
fn arrow_nested_in_product() {
    // (Int -> Int) * Int  →  Mul(Arrow(Int, Int), Int)
    let ExprKind::BinOp {
        op: BinOp::Mul,
        lhs,
        rhs,
    } = parse_set("(Int -> Int) * Int")
    else {
        panic!("expected top-level Mul");
    };
    assert!(matches!(
        lhs.kind,
        ExprKind::BinOp {
            op: BinOp::Arrow,
            ..
        }
    ));
    assert!(matches!(rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"));
}

#[test]
fn arrow_chain_right_associates() {
    // (A -> B -> C)  ==  A -> (B -> C)
    let ExprKind::BinOp {
        op: BinOp::Arrow,
        lhs,
        rhs,
    } = parse_set("(A -> B -> C)")
    else {
        panic!("expected outer Arrow");
    };
    assert!(matches!(lhs.kind, ExprKind::Var(ref s) if s.0 == "A"));
    let ExprKind::BinOp {
        op: BinOp::Arrow,
        lhs: inner_lhs,
        rhs: inner_rhs,
    } = rhs.kind
    else {
        panic!("expected nested Arrow on the right, got {:?}", rhs.kind);
    };
    assert!(matches!(inner_lhs.kind, ExprKind::Var(ref s) if s.0 == "B"));
    assert!(matches!(inner_rhs.kind, ExprKind::Var(ref s) if s.0 == "C"));
}

#[test]
fn arrow_as_nested_range() {
    // higher : Int -> (Int -> Int) — the top-level `->` (domain/range
    // separator) is consumed by `parse_item`, not `parse_set_expr`; the
    // *range* itself is a parenthesized nested arrow.
    let items = parse_file("higher : Int -> (Int -> Int)\nhigher(x) = x")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Item::FunctionDef(def) = &items[0] else {
        panic!("expected FunctionDef, got {:?}", items[0]);
    };
    assert!(matches!(
        def.sigs[0].domain.as_ref().unwrap().kind,
        ExprKind::Var(ref s) if s.0 == "Int"
    ));
    assert!(matches!(
        def.sigs[0].range.kind,
        ExprKind::BinOp {
            op: BinOp::Arrow,
            ..
        }
    ));
}

#[test]
fn full_signature_with_function_kind_domain_parses() {
    // apply : (Int -> Int) * Int -> Int
    let items = parse_file("apply : (Int -> Int) * Int -> Int\napply(f, x) = f(x)")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Item::FunctionDef(def) = &items[0] else {
        panic!("expected FunctionDef, got {:?}", items[0]);
    };
    let domain = def.sigs[0]
        .domain
        .as_ref()
        .expect("apply should have a domain");
    assert!(matches!(
        domain.kind,
        ExprKind::BinOp { op: BinOp::Mul, .. }
    ));
}

#[test]
fn plain_grouping_still_works_alongside_arrow() {
    // Regression: ordinary `(expr)` grouping (no `->`) must be unaffected.
    assert!(matches!(
        parse_set("(Int)"),
        ExprKind::Var(ref s) if s.0 == "Int"
    ));
    assert!(matches!(
        parse("(1 + 2) * 3"),
        ExprKind::BinOp { op: BinOp::Mul, .. }
    ));
}

#[test]
fn top_level_signature_arrow_unaffected() {
    // Regression: the ordinary, non-nested top-level `name : domain -> range`
    // split (consumed by `parse_item`, not the general Pratt loop) still works.
    let items =
        parse_file("abs : Int -> Nat\nabs(x) = x").unwrap_or_else(|e| panic!("parse error: {e}"));
    let Item::FunctionDef(def) = &items[0] else {
        panic!("expected FunctionDef, got {:?}", items[0]);
    };
    assert!(matches!(
        def.sigs[0].domain.as_ref().unwrap().kind,
        ExprKind::Var(ref s) if s.0 == "Int"
    ));
    assert!(matches!(def.sigs[0].range.kind, ExprKind::Var(ref s) if s.0 == "Nat"));
}
