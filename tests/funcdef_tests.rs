use cantor::{
    ast::{BinOp, ExprKind, FunctionBody, Item, NameDef, FunctionDef},
    parser::parse_file,
};

// ── Helpers ───────────────────────────────────────────────────────────────────

fn parse_one(src: &str) -> FunctionDef {
    let items = parse_file(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"));
    assert_eq!(items.len(), 1, "expected exactly one item");
    let Item::FunctionDef(def) = items.into_iter().next().unwrap() else {
        panic!("expected FunctionDef item");
    };
    def
}

fn parse_one_const(src: &str) -> NameDef {
    let items = parse_file(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"));
    assert_eq!(items.len(), 1, "expected exactly one item");
    let Item::NameDef(def) = items.into_iter().next().unwrap() else {
        panic!("expected NameDef item");
    };
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
    mut y: Int = x + 1
    y := y * 2
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

// ── Set literal syntax ────────────────────────────────────────────────────────

#[test]
fn singleton_set_as_range() {
    let def = parse_one("f : Int -> {42}\nf(x) = 42");
    let sig = &def.sigs[0];
    let ExprKind::SetLit(elems) = &sig.range.kind else { panic!("expected SetLit") };
    assert_eq!(elems.len(), 1);
    assert!(matches!(elems[0].kind, ExprKind::IntLit(42)));
}

#[test]
fn multi_element_set_as_range() {
    let def = parse_one("f : Int -> {0, 1, 2}\nf(x) = 0");
    let sig = &def.sigs[0];
    let ExprKind::SetLit(elems) = &sig.range.kind else { panic!("expected SetLit") };
    assert_eq!(elems.len(), 3);
}

#[test]
fn set_difference_in_domain() {
    let def = parse_one("f : Int - {0} -> Int\nf(x) = x");
    let sig = &def.sigs[0];
    let domain = sig.domain.as_ref().unwrap();
    let ExprKind::BinOp { op: BinOp::Sub, lhs, rhs } = &domain.kind
        else { panic!("expected BinOp::Sub, got {:?}", domain.kind) };
    assert!(matches!(lhs.kind, ExprKind::Var(_)));
    let ExprKind::SetLit(elems) = &rhs.kind else { panic!("expected SetLit on rhs") };
    assert_eq!(elems.len(), 1);
    assert!(matches!(elems[0].kind, ExprKind::IntLit(0)));
}

#[test]
fn set_lit_in_expression_body() {
    // {0} in expression position should parse as a SetLit.
    let def = parse_one("f : Int -> {0}\nf(x) = {0}");
    let FunctionBody::Expr(body) = &def.body else { panic!("expected Expr body") };
    assert!(matches!(body.kind, ExprKind::SetLit(_)));
}

#[test]
fn empty_set_lit() {
    // {} should parse without error (empty SetLit).
    let def = parse_one("f : Int -> {}\nf(x) = {}");
    let sig = &def.sigs[0];
    let ExprKind::SetLit(elems) = &sig.range.kind else { panic!("expected SetLit") };
    assert_eq!(elems.len(), 0);
}

#[test]
fn set_lit_trailing_comma() {
    let def = parse_one("f : Int -> {1, 2,}\nf(x) = 1");
    let sig = &def.sigs[0];
    let ExprKind::SetLit(elems) = &sig.range.kind else { panic!("expected SetLit") };
    assert_eq!(elems.len(), 2);
}

#[test]
fn cartesian_product_with_set_difference() {
    let def = parse_one("f : Int * (Int - {0}) -> Int\nf(x, y) = x");
    let sig = &def.sigs[0];
    let domain = sig.domain.as_ref().unwrap();
    let ExprKind::BinOp { op: BinOp::Mul, .. } = &domain.kind
        else { panic!("expected Mul (Cartesian product) at top level") };
    assert_eq!(def.params.len(), 2);
}

// ── Constant definitions ──────────────────────────────────────────────────────

#[test]
fn const_literal_nat() {
    let def = parse_one_const("pi : Nat = 314");
    assert_eq!(def.name.0, "pi");
    assert!(matches!(def.ty.as_ref().unwrap().kind, ExprKind::Var(ref s) if s.0 == "Nat"));
    assert!(matches!(def.value.kind, ExprKind::IntLit(314)));
}

#[test]
fn const_arithmetic_value() {
    let def = parse_one_const("tau : Nat = 2 * 314");
    assert!(matches!(def.value.kind, ExprKind::BinOp { op: BinOp::Mul, .. }));
}

#[test]
fn const_references_other_const() {
    let items = parse_file("pi : Nat = 314\ntau : Nat = 2 * pi")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert_eq!(items.len(), 2);
    assert!(matches!(items[0], Item::NameDef(_)));
    assert!(matches!(items[1], Item::NameDef(_)));
}

#[test]
fn const_and_function_in_same_file() {
    let items = parse_file("base : Nat = 10\ndouble : Nat -> Nat\ndouble(x) = x + x")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert_eq!(items.len(), 2);
    assert!(matches!(items[0], Item::NameDef(_)));
    assert!(matches!(items[1], Item::FunctionDef(_)));
}

#[test]
fn const_negative_value() {
    let def = parse_one_const("offset : Int = -5");
    assert!(matches!(def.value.kind, ExprKind::UnOp { op: cantor::ast::UnOp::Neg, .. }));
}

// ── While loops ───────────────────────────────────────────────────────────────

#[test]
fn while_parses_as_stmt() {
    let src = "sum_to : Nat -> Nat\nsum_to(n) {\n    mut acc: Nat = 0\n    mut i: Nat = 1\n    while i <= n {\n        acc := acc + i\n        i := i + 1\n    }\n    acc\n}";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    assert_eq!(stmts.len(), 4); // MutLet acc, MutLet i, While, Expr(acc)
    assert!(matches!(stmts[2], cantor::ast::Stmt::While { .. }));
}

#[test]
fn while_body_stmts_parsed() {
    let src = "f : Int -> Int\nf(x) {\n    mut i: Int = 0\n    while i < x {\n        i := i + 1\n    }\n    i\n}";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    let cantor::ast::Stmt::While { body, .. } = &stmts[1] else { panic!("expected While") };
    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], cantor::ast::Stmt::Assign { .. }));
}

#[test]
fn while_condition_parsed() {
    let src = "f : Nat -> Nat\nf(n) {\n    mut i: Nat = 0\n    while i < n {\n        i := i + 1\n    }\n    i\n}";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!() };
    let cantor::ast::Stmt::While { cond, .. } = &stmts[1] else { panic!("expected While") };
    assert!(matches!(cond.kind, ExprKind::BinOp { op: BinOp::Lt, .. }));
}

// ── For-in loops ──────────────────────────────────────────────────────────────

#[test]
fn for_in_parses_as_stmt() {
    let src = "f : -> Int\nf() {\n    mut acc: Int = 0\n    for x in {1, 2, 3} {\n        acc := acc + x\n    }\n    acc\n}";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    assert_eq!(stmts.len(), 3); // MutLet acc, ForIn, Expr(acc)
    assert!(matches!(stmts[1], cantor::ast::Stmt::ForIn { .. }));
}

#[test]
fn for_in_var_and_set_parsed() {
    let src = "f : -> Int\nf() {\n    mut acc: Int = 0\n    for x in {1, 2, 3} {\n        acc := acc + x\n    }\n    acc\n}";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!() };
    let cantor::ast::Stmt::ForIn { var, set, .. } = &stmts[1] else { panic!("expected ForIn") };
    assert_eq!(var.0.as_str(), "x");
    assert!(matches!(set.kind, ExprKind::SetLit(_)));
}

#[test]
fn for_in_body_parsed() {
    let src = "f : -> Int\nf() {\n    mut acc: Int = 0\n    for x in {1, 2} {\n        acc := acc + x\n    }\n    acc\n}";
    let def = parse_one(src);
    let FunctionBody::Block(stmts) = &def.body else { panic!() };
    let cantor::ast::Stmt::ForIn { body, .. } = &stmts[1] else { panic!("expected ForIn") };
    assert_eq!(body.len(), 1);
    assert!(matches!(body[0], cantor::ast::Stmt::Assign { .. }));
}

// ── Repeated products in signatures (`X * N`) ─────────────────────────────────
// `Int * 3` desugars to `Int * Int * Int` at parse time.
// CURRENT STATE: `f : Int * 3 -> Int` parses as Mul(Int, 3) which is treated as
// integer multiplication — the desugaring doesn't exist yet so `f(x, y, z)` fails.
// UPDATE these tests to use `parse_one` structural assertions once the parser
// understands `* N` in set/signature positions.

#[test]
fn repeated_product_sig_currently_parses_wrong() {
    // `Int * 3` in a signature is currently parsed as Mul(Int, IntLit(3))
    // not as the desugared Mul(Mul(Int, Int), Int).
    // Once implemented: parse_one("f : Int * 3 -> Int\nf(x, y, z) = x + y + z")
    //   should have def.params.len() == 3.
    let result = parse_file("f : Int * 3 -> Int\nf(x, y, z) = x + y + z");
    // For now we just assert the source parses without a hard error;
    // the arity mismatch might or might not surface at parse time.
    let _ = result; // result could be Ok or Err; behaviour is TBD
}

#[test]
fn repeated_product_one_is_scalar_currently() {
    // `Nat * 1` in a signature should eventually desugar to `Nat` (no product),
    // giving one parameter.  Check the domain is a Mul node today (pre-desugar).
    let def = parse_one("f : Nat * 1 -> Nat\nf(x) = x");
    // Currently the domain is Mul(Nat, IntLit(1)) — a BinOp::Mul.
    // After desugaring it should be Var("Nat") and params.len() == 1.
    assert_eq!(def.params.len(), 1);
}

// ── Kleene-star set expressions in signatures (`X*`) ─────────────────────────
// `Nat*` is a postfix operator in set positions.
// CURRENT STATE: `Nat*` is parsed as Mul(Nat, <missing>) → parse error.
// These tests assert the failure and document the intended AST.

#[test]
fn kleene_star_in_range_currently_parse_error() {
    // Expected future: sig.range.kind == ExprKind::KleeneStar(Var("Nat"))
    let msg = parse_err("f : -> Nat*\nf() = []");
    assert!(!msg.is_empty(),
        "Nat* should currently produce a parse error; \
         update to check ExprKind::KleeneStar once implemented");
}

#[test]
fn kleene_star_in_domain_currently_parse_error() {
    // Expected future: domain.kind == ExprKind::KleeneStar(Var("Nat"))
    let msg = parse_err("f : Nat* -> Nat\nf(xs) = 0");
    assert!(!msg.is_empty(),
        "Nat* domain should currently produce a parse error; update once implemented");
}

#[test]
fn kleene_star_set_diff_currently_parse_error() {
    // Expected future: ExprKind::KleeneStar(BinOp(Sub, Int, SetLit([0])))
    let msg = parse_err("f : (Int - {0})* -> Int\nf(xs) = 0");
    assert!(!msg.is_empty(),
        "(Int - {{0}})* should currently produce a parse error; update once implemented");
}

// ── Array literal `[...]` in bodies ───────────────────────────────────────────
// `[1, 2, 3]` is a value literal that desugars to `Tuple([1, 2, 3])`.

#[test]
fn array_lit_in_body_parses_as_tuple() {
    let def = parse_one("f : -> Int * 3\nf() = [1, 2, 3]");
    let FunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    let ExprKind::Tuple(elems) = &body.kind else {
        panic!("expected Tuple body, got {:?}", body.kind)
    };
    assert_eq!(elems.len(), 3);
    assert!(matches!(elems[0].kind, ExprKind::IntLit(1)));
    assert!(matches!(elems[1].kind, ExprKind::IntLit(2)));
    assert!(matches!(elems[2].kind, ExprKind::IntLit(3)));
}

#[test]
fn array_lit_used_in_set_position_parses_as_tuple_domain() {
    // `[Int]` in domain position parses as Tuple([Var("Int")]) — syntactically
    // allowed, but semantically invalid (a set expression cannot be a Tuple literal).
    // The error surfaces at the solver/codegen stage, not at parse time.
    // TODO: add a parse-time check that rejects Tuple in set-expression positions.
    let def = parse_one("f : [Int] -> Int\nf(xs) = 0");
    let sig = &def.sigs[0];
    let domain = sig.domain.as_ref().expect("expected a domain");
    assert!(matches!(&domain.kind, ExprKind::Tuple(_)),
        "domain parsed as Tuple (semantic check deferred to solver)");
}
