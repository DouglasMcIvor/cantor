//! Elaborator tests: the position-disambiguation cases that caused real bugs
//! before elaboration existed (the lhs/rhs swap, `+` always assuming
//! set-builder context) — `A * B` in domain position must mean Cartesian
//! product while `a * b` in a body means multiplication, `{0} + NatPos` must
//! stay tagged (forced-disjoint), and aliases must resolve transparently.

use cantor::ast::Item;
use cantor::kind::Kind;
use cantor::parser::parse_file;
use cantor::semantics::elaborate::elaborate;
use cantor::semantics::tree::{SemExprKind, SemFunctionBody, SemItem};

fn elaborate_src(src: &str) -> Vec<SemItem> {
    let items: Vec<Item> = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    elaborate(&items).unwrap_or_else(|e| panic!("elaborate error: {e}"))
}

/// Elaborates `src` and returns the function named `name` — tolerates extra
/// `NameDef` items (aliases, distinct sets) alongside the function under test.
fn elaborate_function(src: &str, name: &str) -> cantor::semantics::tree::SemFunctionDef {
    let items = elaborate_src(src);
    items.into_iter().find_map(|item| match item {
        SemItem::FunctionDef(def) if def.name.0 == name => Some(def),
        _ => None,
    }).unwrap_or_else(|| panic!("no function named `{name}` in elaborated output"))
}

fn only_function(src: &str) -> cantor::semantics::tree::SemFunctionDef {
    let items = elaborate_src(src);
    assert_eq!(items.len(), 1, "expected exactly one item");
    let SemItem::FunctionDef(def) = items.into_iter().next().unwrap() else {
        panic!("expected a FunctionDef item");
    };
    def
}

// ── `*` disambiguation: Cartesian product (domain) vs multiplication (body) ──

#[test]
fn star_in_domain_is_cartesian_product() {
    let def = only_function("f : Int * Bool -> Int\nf(a, b) = 0");
    let domain = def.sigs[0].domain.as_ref().expect("domain");
    assert!(matches!(domain.kind, SemExprKind::CartesianProduct(_, _)), "expected CartesianProduct, got {:?}", domain.kind);
    // Asymmetric arms confirm lhs/rhs aren't swapped (the bug fixed last session).
    assert_eq!(domain.kind_of, Kind::Tuple(vec![Kind::Int, Kind::Bool]));
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int, Kind::Bool]);
}

#[test]
fn star_in_body_is_multiplication() {
    let def = only_function("f : Int * Int -> Int\nf(a, b) = a * b");
    let SemFunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    assert!(matches!(body.kind, SemExprKind::Mul(_, _)), "expected Mul, got {:?}", body.kind);
    assert_eq!(body.kind_of, Kind::Int);
}

#[test]
fn same_function_disambiguates_plus_per_position() {
    // The domain's `+` is a disjoint union (forced-tagged); the body's `+`
    // on the very same parameter is ordinary arithmetic. One function,
    // both meanings, resolved purely from where each `+` appears.
    let def = only_function("h : {0} + NatPos -> Int\nh(x) = x + 1");

    let domain = def.sigs[0].domain.as_ref().expect("domain");
    assert!(matches!(domain.kind, SemExprKind::DisjointUnion(_, _)), "expected DisjointUnion, got {:?}", domain.kind);
    assert_eq!(domain.kind_of, Kind::TaggedUnion(vec![Kind::Int, Kind::Int]));
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::TaggedUnion(vec![Kind::Int, Kind::Int])]);

    let SemFunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    assert!(matches!(body.kind, SemExprKind::Add(_, _)), "expected Add, got {:?}", body.kind);
    assert_eq!(body.kind_of, Kind::Int);
}

// ── `+` forces a tag even when both arms share a Kind (mirrors `distinct`) ───

#[test]
fn disjoint_union_stays_tagged_for_same_kind_arms() {
    let def = only_function("accept_nat : {0} + NatPos -> Nat\naccept_nat(x) = x");
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::TaggedUnion(vec![Kind::Int, Kind::Int])]);
}

// ── `|` collapses same-kind arms (no tag), unlike `+` ────────────────────────

#[test]
fn union_of_same_kind_collapses_no_tag() {
    let def = only_function("g : Nat | NatPos -> Int\ng(x) = x");
    let domain = def.sigs[0].domain.as_ref().expect("domain");
    assert!(matches!(&domain.kind, SemExprKind::BinOp { op: cantor::ast::BinOp::Union, .. }));
    assert_eq!(domain.kind_of, Kind::Int);
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int]);
}

// ── Aliases resolve transparently through the symbol table ──────────────────

#[test]
fn alias_resolves_to_underlying_kind() {
    let def = elaborate_function("MyNat = Nat\nf : MyNat -> MyNat\nf(x) = x", "f");
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int]);
    assert_eq!(def.sigs[0].return_kind, Kind::Int);
}

#[test]
fn distinct_set_is_int_backed_but_disjoint() {
    let def = elaborate_function("Litre = distinct Nat\nf : Litre -> Litre\nf(x) = x", "f");
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int]);
}

// ── Block bodies: `let` constraints are set position, values are value position ─

#[test]
fn let_constraint_is_set_position_value_is_value_position() {
    let def = only_function(
        "f : Int * Int -> Int\nf(a, b) {\n s : Int * Int = (a, b)\n s.0 * s.1\n}"
    );
    let SemFunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    let cantor::semantics::tree::SemStmt::Let { constraint, value, .. } = &stmts[0] else {
        panic!("expected a Let statement, got {:?}", stmts[0])
    };
    // `Int * Int` constraint → Cartesian product (set position).
    assert!(matches!(constraint.kind, SemExprKind::CartesianProduct(_, _)));
    assert_eq!(constraint.kind_of, Kind::Tuple(vec![Kind::Int, Kind::Int]));
    // `(a, b)` value → an ordinary tuple value (value position).
    assert!(matches!(value.kind, SemExprKind::Tuple(_)));
}

// ── `in`'s RHS is always set position, even inside a value-position body ────

#[test]
fn in_rhs_is_set_position_regardless_of_surrounding_position() {
    let def = only_function("f : Int -> Bool\nf(x) = x * 2 in NatPos");
    let SemFunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    let SemExprKind::BinOp { op: cantor::ast::BinOp::In, lhs, rhs } = &body.kind else {
        panic!("expected a top-level `in`, got {:?}", body.kind)
    };
    // LHS (`x * 2`) is a value-position multiplication.
    assert!(matches!(lhs.kind, SemExprKind::Mul(_, _)));
    // RHS (`NatPos`) is resolved as a set, not a local variable lookup.
    assert_eq!(rhs.kind_of, Kind::Int);
    assert_eq!(body.kind_of, Kind::Bool);
}
