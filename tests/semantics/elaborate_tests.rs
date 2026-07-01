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

// ── Stage 2a: `if`/`++`/vector-indexing gaps closed via kind::merge_* ───────

#[test]
fn if_merges_tuple_and_scalar_branches_into_tagged_union() {
    // Neither branch is already a TaggedUnion, but one is a Tuple — merges
    // into a fresh 2-arm union (mirrors codegen's `IfMerge::NewTaggedUnion`).
    let def = only_function("f : Nat -> (Nat * Nat) | Nat\nf(x) = if x > 0 then (x, x) else x");
    let SemFunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    assert_eq!(body.kind_of, Kind::TaggedUnion(vec![Kind::Tuple(vec![Kind::Int, Kind::Int]), Kind::Int]));
}

#[test]
fn if_extends_existing_tagged_union_with_new_arm() {
    // `then` is already a 2-arm TaggedUnion (from the inner `if`); `else` is a
    // plain Bool appended as a third arm (mirrors `IfMerge::AppendElseArm`).
    let def = only_function(
        "f : Nat -> (Nat * Nat) | Nat | Bool\nf(x) = if x > 2 then (if x > 5 then (x, x) else x) else false"
    );
    let SemFunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    assert_eq!(body.kind_of, Kind::TaggedUnion(vec![Kind::Tuple(vec![Kind::Int, Kind::Int]), Kind::Int, Kind::Bool]));
}

#[test]
fn if_merges_two_different_tagged_unions() {
    // Both branches are already (different) TaggedUnions — arms dedup, then's
    // arms first (mirrors `IfMerge::MergeTaggedUnions`).
    let def = only_function(
        "f : Nat -> (Nat * Nat) | Nat | Bool\n\
         f(x) = if x > 3 then (if x > 5 then (x, x) else x) else (if x > 1 then false else (x, x + 1))"
    );
    let SemFunctionBody::Expr(body) = &def.body else { panic!("expected expr body") };
    assert_eq!(body.kind_of, Kind::TaggedUnion(vec![Kind::Tuple(vec![Kind::Int, Kind::Int]), Kind::Int, Kind::Bool]));
}

#[test]
fn if_with_unmergeable_branch_kinds_fails_loudly() {
    // Int vs Bool, neither a Tuple nor a TaggedUnion — no coercion path
    // exists, so elaboration must error rather than guess a Kind.
    let items = parse_file("f : Nat -> Int\nf(x) = if x > 0 then 1 else true")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(elaborate(&items).is_err(), "expected elaborate to reject unmergeable if-branches");
}

#[test]
fn concat_coerces_tuple_literal_to_vector() {
    // lhs is a literal Tuple; rhs (`xs`, constrained to `Nat*`) is already a
    // Vector — lhs must be coerced, and the result Kind is the shared Vector
    // element Kind.
    let def = only_function("f : Nat -> Nat*\nf(x) {\n xs : Nat* = [x]\n (x, x) ++ xs\n}");
    let SemFunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    let cantor::semantics::tree::SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(e.kind_of, Kind::Vector(Box::new(Kind::Int)));
}

#[test]
fn indexing_vector_of_tuples_yields_the_tuple_kind_unchanged() {
    let def = only_function("f : -> Nat\nf() {\n xs : (Nat * Nat)* = [(1, 2), (3, 4)]\n xs[0]\n}");
    let SemFunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    let cantor::semantics::tree::SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(e.kind_of, Kind::Tuple(vec![Kind::Int, Kind::Int]));
}

#[test]
fn indexing_vector_of_tagged_unions_yields_the_union_kind_unchanged() {
    let def = only_function(
        "f : -> Nat\nf() {\n xs : (Nat | (Nat * Bool))* = [1, (2, true)]\n xs[0]\n}"
    );
    let SemFunctionBody::Block(stmts) = &def.body else { panic!("expected block body") };
    let cantor::semantics::tree::SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(e.kind_of, Kind::TaggedUnion(vec![Kind::Int, Kind::Tuple(vec![Kind::Int, Kind::Bool])]));
}
