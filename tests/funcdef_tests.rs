use cantor::{
    ast::{BinOp, ExprKind, FunctionBody, Item},
    parser::parse_file,
};

// ── Helpers ───────────────────────────────────────────────────────────────────

fn parse_one(src: &str) -> cantor::ast::FunctionDef {
    let items = parse_file(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"));
    assert_eq!(items.len(), 1, "expected exactly one item");
    let Item::FunctionDef(def) = items.into_iter().next().unwrap();
    def
}

fn parse_err(src: &str) -> String {
    parse_file(src)
        .err()
        .unwrap_or_else(|| panic!("expected parse error for {src:?}"))
        .to_string()
}

// ── Signature + pure body ─────────────────────────────────────────────────────

#[test]
fn simple_sig_and_expr_body() {
    let def = parse_one("double : Int -> Int\ndouble(x) = x + x");
    assert_eq!(def.name.0, "double");
    assert_eq!(def.sigs.len(), 1);
    assert_eq!(def.params.len(), 1);
    assert_eq!(def.params[0].name.0, "x");
    assert!(matches!(def.body, FunctionBody::Expr(_)));
}

#[test]
fn sig_domain_and_range_are_variables() {
    let def = parse_one("f : A -> B\nf(x) = x");
    let sig = &def.sigs[0];
    let domain = sig.domain.as_ref().expect("expected a domain expr");
    assert!(matches!(&domain.kind, ExprKind::Var(s) if s.0 == "A"));
    assert!(matches!(&sig.range.kind, ExprKind::Var(s) if s.0 == "B"));
}

#[test]
fn cartesian_product_domain() {
    // `*` in signature position means Cartesian product (semantic, not arithmetic)
    let def = parse_one("add : Int * Int -> Int\nadd(x, y) = x + y");
    assert_eq!(def.params.len(), 2);
    let domain = def.sigs[0].domain.as_ref().expect("expected a domain expr");
    assert!(matches!(domain.kind, ExprKind::BinOp { op: BinOp::Mul, .. }));
}

#[test]
fn if_then_else_body() {
    let def = parse_one("abs : Int -> Int\nabs(x) = if x >= 0 then x else -x");
    let FunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    assert!(matches!(body.kind, ExprKind::If { .. }));
}

#[test]
fn if_cond_then_else_structure() {
    let def = parse_one("abs : Int -> Int\nabs(x) = if x >= 0 then x else -x");
    let FunctionBody::Expr(body) = &def.body else { panic!() };
    let ExprKind::If { cond, then_expr, else_expr } = &body.kind else { panic!() };
    // Condition is x >= 0
    assert!(matches!(cond.kind, ExprKind::BinOp { op: BinOp::Ge, .. }));
    // Then branch is x
    assert!(matches!(then_expr.kind, ExprKind::Var(_)));
    // Else branch is -x
    assert!(matches!(else_expr.kind, ExprKind::UnOp { .. }));
}

#[test]
fn no_arg_function() {
    // Zero-arg functions use `-> Set` with an empty domain (no `Unit`).
    let def = parse_one("zero : -> Int\nzero() = 0");
    assert_eq!(def.params.len(), 0);
    assert!(def.sigs[0].domain.is_none(), "zero-arg sig should have no domain");
    assert!(matches!(def.body, FunctionBody::Expr(_)));
}

#[test]
fn function_call_in_body() {
    let def = parse_one("quad : Int -> Int\nquad(x) = double(double(x))");
    let FunctionBody::Expr(body) = &def.body else { panic!() };
    assert!(matches!(body.kind, ExprKind::Call { .. }));
}

// ── Block body ────────────────────────────────────────────────────────────────

#[test]
fn block_body() {
    let src = "f : Int -> Int\nf(x) { x + 1 }";
    let def = parse_one(src);
    assert!(matches!(def.body, FunctionBody::Block(_)));
}

#[test]
fn block_with_mut_and_assign() {
    let src = r#"
f : Int -> Int
f(x) {
    mut y = x + 1
    y = y * 2
    y
}
"#;
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    assert_eq!(stmts.len(), 3);
    assert!(matches!(stmts[0], cantor::ast::Stmt::MutLet { .. }));
    assert!(matches!(stmts[1], cantor::ast::Stmt::Assign { .. }));
    assert!(matches!(stmts[2], cantor::ast::Stmt::Expr(_)));
}

#[test]
fn block_with_assert() {
    let src = "f : Nat -> Nat\nf(x) { assert x in Nat\nx * 2 }";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    assert!(matches!(stmts[0], cantor::ast::Stmt::Assert { .. }));
}

#[test]
fn block_with_assume() {
    let src = "f : Int -> Nat\nf(x) { assume x in Nat\nx }";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!() };
    assert!(matches!(stmts[0], cantor::ast::Stmt::Assume { .. }));
}

// ── Multiple signatures ───────────────────────────────────────────────────────

#[test]
fn multiple_signatures() {
    let src = r#"
abs : Int -> Nat
abs : Float -> Float
abs(x) = if x >= 0 then x else -x
"#;
    let def = parse_one(src);
    assert_eq!(def.sigs.len(), 2);
}

// ── Multiple top-level items ──────────────────────────────────────────────────

#[test]
fn two_function_defs() {
    let src = "double : Int -> Int\ndouble(x) = x + x\ntriple : Int -> Int\ntriple(x) = x + x + x";
    let items = parse_file(src).unwrap();
    assert_eq!(items.len(), 2);
}

// ── Error cases ───────────────────────────────────────────────────────────────

#[test]
fn missing_arrow_in_sig() {
    let msg = parse_err("f : Int Int\nf(x) = x");
    assert!(!msg.is_empty(), "expected an error");
}

#[test]
fn impl_name_must_match_sig() {
    let msg = parse_err("foo : Int -> Int\nbar(x) = x");
    assert!(!msg.is_empty(), "expected mismatch error");
}

#[test]
fn missing_body() {
    let msg = parse_err("f : Int -> Int\nf(x)");
    assert!(!msg.is_empty(), "expected error for missing body");
}
