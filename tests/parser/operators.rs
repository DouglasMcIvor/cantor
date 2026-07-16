use cantor::ast::{BinOp, ExprKind, UnOp};

use super::helpers::*;

// ── Arithmetic ────────────────────────────────────────────────────────────────

#[test]
fn parse_add() {
    assert!(matches!(
        parse("1 + 2"),
        ExprKind::BinOp { op: BinOp::Add, .. }
    ));
}

#[test]
fn parse_mul_binds_tighter_than_add() {
    // 1 + 2 * 3  →  Add(1, Mul(2, 3))
    let ExprKind::BinOp { op, rhs, .. } = parse("1 + 2 * 3") else {
        panic!()
    };
    assert_eq!(op, BinOp::Add);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::Mul, .. }));
}

#[test]
fn parse_add_is_left_assoc() {
    // 1 + 2 + 3  →  Add(Add(1, 2), 3)
    assert_eq!(
        inorder_ops(&parse("1 + 2 + 3")),
        vec![BinOp::Add, BinOp::Add]
    );
    let ExprKind::BinOp { lhs, .. } = parse("1 + 2 + 3") else {
        panic!()
    };
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn parse_parens_override_precedence() {
    // (1 + 2) * 3  →  Mul(Add(1, 2), 3)
    let ExprKind::BinOp { op, lhs, .. } = parse("(1 + 2) * 3") else {
        panic!()
    };
    assert_eq!(op, BinOp::Mul);
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn parse_unary_neg() {
    assert!(matches!(parse("-1"), ExprKind::UnOp { op: UnOp::Neg, .. }));
}

#[test]
fn parse_neg_binds_tight() {
    // -x * 2  →  Mul(Neg(x), 2)
    let ExprKind::BinOp { op, lhs, .. } = parse("-x * 2") else {
        panic!()
    };
    assert_eq!(op, BinOp::Mul);
    assert!(matches!(lhs.kind, ExprKind::UnOp { op: UnOp::Neg, .. }));
}

// ── Comparisons ───────────────────────────────────────────────────────────────

#[test]
fn parse_eq() {
    assert!(matches!(
        parse("x == y"),
        ExprKind::BinOp { op: BinOp::Eq, .. }
    ));
}

#[test]
fn parse_ne() {
    assert!(matches!(
        parse("x != y"),
        ExprKind::BinOp { op: BinOp::Ne, .. }
    ));
}

#[test]
fn parse_lt_le_gt_ge() {
    assert!(matches!(
        parse("a < b"),
        ExprKind::BinOp { op: BinOp::Lt, .. }
    ));
    assert!(matches!(
        parse("a <= b"),
        ExprKind::BinOp { op: BinOp::Le, .. }
    ));
    assert!(matches!(
        parse("a > b"),
        ExprKind::BinOp { op: BinOp::Gt, .. }
    ));
    assert!(matches!(
        parse("a >= b"),
        ExprKind::BinOp { op: BinOp::Ge, .. }
    ));
}

#[test]
fn parse_comparison_lower_than_arithmetic() {
    // 1 + 2 == 3  →  Eq(Add(1, 2), 3)
    let ExprKind::BinOp { op, lhs, .. } = parse("1 + 2 == 3") else {
        panic!()
    };
    assert_eq!(op, BinOp::Eq);
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

// ── Membership ────────────────────────────────────────────────────────────────

#[test]
fn parse_in() {
    assert!(matches!(
        parse("x in S"),
        ExprKind::BinOp { op: BinOp::In, .. }
    ));
}

#[test]
fn parse_not_in() {
    assert!(matches!(
        parse("x not in S"),
        ExprKind::BinOp {
            op: BinOp::NotIn,
            ..
        }
    ));
}

// ── Set operators ─────────────────────────────────────────────────────────────

#[test]
fn parse_union() {
    assert!(matches!(
        parse("A | B"),
        ExprKind::BinOp {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn parse_intersect() {
    assert!(matches!(
        parse("A & B"),
        ExprKind::BinOp {
            op: BinOp::Intersect,
            ..
        }
    ));
}

#[test]
fn parse_sym_diff() {
    assert!(matches!(
        parse("A ^ B"),
        ExprKind::BinOp {
            op: BinOp::SymDiff,
            ..
        }
    ));
}

#[test]
fn parse_set_op_precedence() {
    // A | B & C  →  Union(A, Intersect(B, C))  because & > |
    let ExprKind::BinOp { op, rhs, .. } = parse("A | B & C") else {
        panic!()
    };
    assert_eq!(op, BinOp::Union);
    assert!(matches!(
        rhs.kind,
        ExprKind::BinOp {
            op: BinOp::Intersect,
            ..
        }
    ));
}

// ── Logic ─────────────────────────────────────────────────────────────────────

#[test]
fn parse_and() {
    assert!(matches!(
        parse("a and b"),
        ExprKind::BinOp { op: BinOp::And, .. }
    ));
}

#[test]
fn parse_or() {
    assert!(matches!(
        parse("a or b"),
        ExprKind::BinOp { op: BinOp::Or, .. }
    ));
}

#[test]
fn parse_not() {
    assert!(matches!(
        parse("not x"),
        ExprKind::UnOp { op: UnOp::Not, .. }
    ));
}

#[test]
fn parse_not_absorbs_comparison() {
    // `not x == y`  →  Not(Eq(x, y))  — not does NOT steal `x` alone
    let ExprKind::UnOp { op, expr } = parse("not x == y") else {
        panic!()
    };
    assert_eq!(op, UnOp::Not);
    assert!(matches!(expr.kind, ExprKind::BinOp { op: BinOp::Eq, .. }));
}

#[test]
fn parse_not_does_not_absorb_and() {
    // `not x and y`  →  And(Not(x), y)
    let ExprKind::BinOp { op, lhs, .. } = parse("not x and y") else {
        panic!()
    };
    assert_eq!(op, BinOp::And);
    assert!(matches!(lhs.kind, ExprKind::UnOp { op: UnOp::Not, .. }));
}

#[test]
fn parse_and_tighter_than_or() {
    // a or b and c  →  Or(a, And(b, c))
    let ExprKind::BinOp { op, rhs, .. } = parse("a or b and c") else {
        panic!()
    };
    assert_eq!(op, BinOp::Or);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::And, .. }));
}
