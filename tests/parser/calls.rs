use cantor::ast::{BinOp, ExprKind};

use super::helpers::*;

// ── Function calls ────────────────────────────────────────────────────────────

#[test]
fn parse_call_no_args() {
    assert!(matches!(parse("f()"), ExprKind::Call { .. }));
}

#[test]
fn parse_call_one_arg() {
    let ExprKind::Call { callee, args } = parse("f(x)") else {
        panic!()
    };
    assert_eq!(callee.0, "f");
    assert_eq!(args.len(), 1);
}

#[test]
fn parse_call_multiple_args() {
    let ExprKind::Call { callee, args } = parse("add(1, 2, 3)") else {
        panic!()
    };
    assert_eq!(callee.0, "add");
    assert_eq!(args.len(), 3);
}

#[test]
fn parse_nested_call() {
    // f(g(x))
    let ExprKind::Call { args, .. } = parse("f(g(x))") else {
        panic!()
    };
    assert!(matches!(args[0].kind, ExprKind::Call { .. }));
}

#[test]
fn parse_call_in_expression() {
    // double(x) + 1
    let ExprKind::BinOp { op, lhs, .. } = parse("double(x) + 1") else {
        panic!()
    };
    assert_eq!(op, BinOp::Add);
    assert!(matches!(lhs.kind, ExprKind::Call { .. }));
}
