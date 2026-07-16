use cantor::ast::{BinOp, ExprKind};

use super::helpers::*;

// ── Homogeneous tuple literals `[...]` ────────────────────────────────────────
// `[a, b, c]` desugars to `Tuple([a, b, c])` at parse time.
// TODO: once range inference is available, enforce that all elements belong to
// the same set X (homogeneity constraint).

#[test]
fn parse_array_lit_three_ints() {
    let kind = parse("[1, 2, 3]");
    let ExprKind::Tuple(elems) = kind else {
        panic!("expected Tuple, got {kind:?}")
    };
    assert_eq!(elems.len(), 3);
    assert!(matches!(elems[0].kind, ExprKind::IntLit(1)));
    assert!(matches!(elems[1].kind, ExprKind::IntLit(2)));
    assert!(matches!(elems[2].kind, ExprKind::IntLit(3)));
}

#[test]
fn parse_array_lit_bool_elements() {
    let kind = parse("[true, false]");
    let ExprKind::Tuple(elems) = kind else {
        panic!("expected Tuple, got {kind:?}")
    };
    assert_eq!(elems.len(), 2);
    assert!(matches!(elems[0].kind, ExprKind::BoolLit(true)));
    assert!(matches!(elems[1].kind, ExprKind::BoolLit(false)));
}

#[test]
fn parse_empty_array_lit() {
    let kind = parse("[]");
    assert!(matches!(kind, ExprKind::Tuple(elems) if elems.is_empty()));
}

// ── Bracket index `x[N]` — alias for `x.N` ───────────────────────────────────

#[test]
fn parse_bracket_index_is_proj() {
    // x[0]  →  Proj { base: Var("x"), index: 0 }
    let ExprKind::Proj { base, index } = parse("x[0]") else {
        panic!("expected Proj")
    };
    assert!(matches!(base.kind, ExprKind::Var(ref s) if s.0 == "x"));
    assert_eq!(index, 0);
}

#[test]
fn parse_bracket_index_two() {
    let ExprKind::Proj { index, .. } = parse("t[2]") else {
        panic!()
    };
    assert_eq!(index, 2);
}

#[test]
fn parse_bracket_index_on_array_lit() {
    // [1, 2, 3][1]  →  Proj { base: Tuple([1,2,3]), index: 1 }
    let ExprKind::Proj { base, index } = parse("[1, 2, 3][1]") else {
        panic!("expected Proj")
    };
    assert!(matches!(base.kind, ExprKind::Tuple(_)));
    assert_eq!(index, 1);
}

#[test]
fn parse_dot_and_bracket_are_equivalent() {
    // x.1  and  x[1]  should produce identical AST nodes (both Proj with index 1).
    let dot = parse("x.1");
    let bracket = parse("x[1]");
    // Both should be Proj with index 1; compare index rather than full AST.
    let ExprKind::Proj { index: di, .. } = dot else {
        panic!()
    };
    let ExprKind::Proj { index: bi, .. } = bracket else {
        panic!()
    };
    assert_eq!(di, bi);
}

// ── Tuple tests ───────────────────────────────────────────────────────────────

#[test]
fn tuple_literal_two_elements() {
    let kind = parse("(1, 2)");
    assert!(matches!(&kind, ExprKind::Tuple(elems) if elems.len() == 2));
    if let ExprKind::Tuple(elems) = &kind {
        assert!(matches!(&elems[0].kind, ExprKind::IntLit(1)));
        assert!(matches!(&elems[1].kind, ExprKind::IntLit(2)));
    }
}

#[test]
fn tuple_literal_three_elements() {
    let kind = parse("(1, 2, 3)");
    assert!(matches!(&kind, ExprKind::Tuple(elems) if elems.len() == 3));
}

#[test]
fn paren_grouping_unchanged() {
    let kind = parse("(1 + 2)");
    assert!(matches!(&kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn nested_tuple() {
    let kind = parse("(1, (2, 3))");
    if let ExprKind::Tuple(elems) = &kind {
        assert_eq!(elems.len(), 2);
        assert!(matches!(&elems[1].kind, ExprKind::Tuple(inner) if inner.len() == 2));
    } else {
        panic!("expected Tuple, got {kind:?}");
    }
}

#[test]
fn proj_simple() {
    let kind = parse("t.0");
    assert!(matches!(&kind, ExprKind::Proj { index: 0, .. }));
}

#[test]
fn proj_chained() {
    let kind = parse("t.0.1");
    if let ExprKind::Proj { base, index: 1 } = &kind {
        assert!(matches!(&base.kind, ExprKind::Proj { index: 0, .. }));
    } else {
        panic!("expected chained Proj, got {kind:?}");
    }
}

#[test]
fn proj_on_call() {
    let kind = parse("f(x).0");
    assert!(matches!(&kind, ExprKind::Proj { index: 0, .. }));
}

#[test]
fn tuple_display_round_trips() {
    let parsed = parse("(1, 2)");
    let displayed = format!("{parsed}");
    assert_eq!(displayed, "(1, 2)");
}

#[test]
fn proj_display_round_trips() {
    let parsed = parse("t.1");
    let displayed = format!("{parsed}");
    assert_eq!(displayed, "t.1");
}
