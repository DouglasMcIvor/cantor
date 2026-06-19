use cantor::{
    ast::{BinOp, ExprKind, UnOp},
    parser::parse_expr,
};

// ── Helpers ───────────────────────────────────────────────────────────────────

fn parse(src: &str) -> ExprKind {
    parse_expr(src).unwrap_or_else(|e| panic!("parse error for {src:?}: {e}")).kind
}

fn parse_err(src: &str) -> String {
    parse_expr(src)
        .err()
        .unwrap_or_else(|| panic!("expected parse error for {src:?}"))
        .to_string()
}

/// Walk the AST and collect BinOp operators in inorder (lhs op rhs) order.
/// Useful for checking associativity without spelling out the full AST.
fn inorder_ops(kind: &ExprKind) -> Vec<BinOp> {
    match kind {
        ExprKind::BinOp { op, lhs, rhs } => {
            let mut ops = inorder_ops(&lhs.kind);
            ops.push(*op);
            ops.extend(inorder_ops(&rhs.kind));
            ops
        }
        _ => vec![],
    }
}

// ── Literals ──────────────────────────────────────────────────────────────────

#[test]
fn parse_int_literal() {
    assert!(matches!(parse("42"), ExprKind::IntLit(42)));
}

#[test]
fn parse_bool_true() {
    assert!(matches!(parse("true"), ExprKind::BoolLit(true)));
}

#[test]
fn parse_bool_false() {
    assert!(matches!(parse("false"), ExprKind::BoolLit(false)));
}

#[test]
fn parse_identifier() {
    assert!(matches!(parse("foo"), ExprKind::Var(sym) if sym.0 == "foo"));
}

// ── Arithmetic ────────────────────────────────────────────────────────────────

#[test]
fn parse_add() {
    assert!(matches!(parse("1 + 2"), ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn parse_mul_binds_tighter_than_add() {
    // 1 + 2 * 3  →  Add(1, Mul(2, 3))
    let ExprKind::BinOp { op, rhs, .. } = parse("1 + 2 * 3") else { panic!() };
    assert_eq!(op, BinOp::Add);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::Mul, .. }));
}

#[test]
fn parse_add_is_left_assoc() {
    // 1 + 2 + 3  →  Add(Add(1, 2), 3)
    assert_eq!(inorder_ops(&parse("1 + 2 + 3")), vec![BinOp::Add, BinOp::Add]);
    let ExprKind::BinOp { lhs, .. } = parse("1 + 2 + 3") else { panic!() };
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn parse_parens_override_precedence() {
    // (1 + 2) * 3  →  Mul(Add(1, 2), 3)
    let ExprKind::BinOp { op, lhs, .. } = parse("(1 + 2) * 3") else { panic!() };
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
    let ExprKind::BinOp { op, lhs, .. } = parse("-x * 2") else { panic!() };
    assert_eq!(op, BinOp::Mul);
    assert!(matches!(lhs.kind, ExprKind::UnOp { op: UnOp::Neg, .. }));
}

// ── Comparisons ───────────────────────────────────────────────────────────────

#[test]
fn parse_eq() {
    assert!(matches!(parse("x == y"), ExprKind::BinOp { op: BinOp::Eq, .. }));
}

#[test]
fn parse_ne() {
    assert!(matches!(parse("x != y"), ExprKind::BinOp { op: BinOp::Ne, .. }));
}

#[test]
fn parse_lt_le_gt_ge() {
    assert!(matches!(parse("a < b"),  ExprKind::BinOp { op: BinOp::Lt, .. }));
    assert!(matches!(parse("a <= b"), ExprKind::BinOp { op: BinOp::Le, .. }));
    assert!(matches!(parse("a > b"),  ExprKind::BinOp { op: BinOp::Gt, .. }));
    assert!(matches!(parse("a >= b"), ExprKind::BinOp { op: BinOp::Ge, .. }));
}

#[test]
fn parse_comparison_lower_than_arithmetic() {
    // 1 + 2 == 3  →  Eq(Add(1, 2), 3)
    let ExprKind::BinOp { op, lhs, .. } = parse("1 + 2 == 3") else { panic!() };
    assert_eq!(op, BinOp::Eq);
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

// ── Membership ────────────────────────────────────────────────────────────────

#[test]
fn parse_in() {
    assert!(matches!(parse("x in S"), ExprKind::BinOp { op: BinOp::In, .. }));
}

#[test]
fn parse_not_in() {
    assert!(matches!(parse("x not in S"), ExprKind::BinOp { op: BinOp::NotIn, .. }));
}

// ── Set operators ─────────────────────────────────────────────────────────────

#[test]
fn parse_union() {
    assert!(matches!(parse("A | B"), ExprKind::BinOp { op: BinOp::Union, .. }));
}

#[test]
fn parse_intersect() {
    assert!(matches!(parse("A & B"), ExprKind::BinOp { op: BinOp::Intersect, .. }));
}

#[test]
fn parse_sym_diff() {
    assert!(matches!(parse("A ^ B"), ExprKind::BinOp { op: BinOp::SymDiff, .. }));
}

#[test]
fn parse_set_op_precedence() {
    // A | B & C  →  Union(A, Intersect(B, C))  because & > |
    let ExprKind::BinOp { op, rhs, .. } = parse("A | B & C") else { panic!() };
    assert_eq!(op, BinOp::Union);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::Intersect, .. }));
}

// ── Logic ─────────────────────────────────────────────────────────────────────

#[test]
fn parse_and() {
    assert!(matches!(parse("a and b"), ExprKind::BinOp { op: BinOp::And, .. }));
}

#[test]
fn parse_or() {
    assert!(matches!(parse("a or b"), ExprKind::BinOp { op: BinOp::Or, .. }));
}

#[test]
fn parse_not() {
    assert!(matches!(parse("not x"), ExprKind::UnOp { op: UnOp::Not, .. }));
}

#[test]
fn parse_not_absorbs_comparison() {
    // `not x == y`  →  Not(Eq(x, y))  — not does NOT steal `x` alone
    let ExprKind::UnOp { op, expr } = parse("not x == y") else { panic!() };
    assert_eq!(op, UnOp::Not);
    assert!(matches!(expr.kind, ExprKind::BinOp { op: BinOp::Eq, .. }));
}

#[test]
fn parse_not_does_not_absorb_and() {
    // `not x and y`  →  And(Not(x), y)
    let ExprKind::BinOp { op, lhs, .. } = parse("not x and y") else { panic!() };
    assert_eq!(op, BinOp::And);
    assert!(matches!(lhs.kind, ExprKind::UnOp { op: UnOp::Not, .. }));
}

#[test]
fn parse_and_tighter_than_or() {
    // a or b and c  →  Or(a, And(b, c))
    let ExprKind::BinOp { op, rhs, .. } = parse("a or b and c") else { panic!() };
    assert_eq!(op, BinOp::Or);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::And, .. }));
}

// ── Function calls ────────────────────────────────────────────────────────────

#[test]
fn parse_call_no_args() {
    assert!(matches!(parse("f()"), ExprKind::Call { .. }));
}

#[test]
fn parse_call_one_arg() {
    let ExprKind::Call { callee, args } = parse("f(x)") else { panic!() };
    assert_eq!(callee.0, "f");
    assert_eq!(args.len(), 1);
}

#[test]
fn parse_call_multiple_args() {
    let ExprKind::Call { callee, args } = parse("add(1, 2, 3)") else { panic!() };
    assert_eq!(callee.0, "add");
    assert_eq!(args.len(), 3);
}

#[test]
fn parse_nested_call() {
    // f(g(x))
    let ExprKind::Call { args, .. } = parse("f(g(x))") else { panic!() };
    assert!(matches!(args[0].kind, ExprKind::Call { .. }));
}

#[test]
fn parse_call_in_expression() {
    // double(x) + 1
    let ExprKind::BinOp { op, lhs, .. } = parse("double(x) + 1") else { panic!() };
    assert_eq!(op, BinOp::Add);
    assert!(matches!(lhs.kind, ExprKind::Call { .. }));
}

// ── Spans ─────────────────────────────────────────────────────────────────────

#[test]
fn span_of_integer_literal() {
    let expr = parse_expr("  42  ").unwrap();
    assert_eq!(expr.span.start, 2);
    assert_eq!(expr.span.end, 4);
}

#[test]
fn span_covers_binop() {
    // "1 + 2" → span should cover the whole expression
    let expr = parse_expr("1 + 2").unwrap();
    assert_eq!(expr.span.start, 0);
    assert_eq!(expr.span.end, 5);
}

// ── Error cases ───────────────────────────────────────────────────────────────

#[test]
fn parse_empty_is_error() {
    assert!(!parse_err("").is_empty());
}

#[test]
fn parse_dangling_operator_is_error() {
    assert!(!parse_err("1 +").is_empty());
}

#[test]
fn parse_unmatched_paren_is_error() {
    assert!(!parse_err("(1 + 2").is_empty());
}

#[test]
fn parse_for_in_expr_is_error() {
    let msg = parse_err("for");
    assert!(msg.contains("not yet"), "expected 'not yet' in: {msg}");
}
