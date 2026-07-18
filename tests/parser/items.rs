use cantor::ast::{BinOp, DefKind, ExprKind, Item};
use cantor::parser::parse_file;

// ── Set definitions ───────────────────────────────────────────────────────────

fn parse_name_def(src: &str) -> (String, DefKind, ExprKind) {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    match items.into_iter().next().unwrap() {
        Item::NameDef(def) => (def.name.0, def.kind, def.value.kind),
        other => panic!("expected NameDef, got {other:?}"),
    }
}

#[test]
fn set_def_set_literal_implicit_alias() {
    let (name, kind, _rhs) = parse_name_def("Colour = {1, 2, 3}");
    assert_eq!(name, "Colour");
    assert_eq!(kind, DefKind::Alias);
}

#[test]
fn set_def_union_implicit_alias() {
    let (name, kind, rhs) = parse_name_def("Animal = Cat | Dog");
    assert_eq!(name, "Animal");
    assert_eq!(kind, DefKind::Alias);
    assert!(matches!(
        rhs,
        ExprKind::BinOp {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn set_def_explicit_alias_keyword() {
    let (name, kind, rhs) = parse_name_def("Animal = alias Cat | Dog");
    assert_eq!(name, "Animal");
    assert_eq!(kind, DefKind::Alias);
    assert!(matches!(
        rhs,
        ExprKind::BinOp {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn set_def_distinct_keyword() {
    let (name, kind, rhs) = parse_name_def("Litre = distinct Float");
    assert_eq!(name, "Litre");
    assert_eq!(kind, DefKind::Distinct);
    assert!(matches!(rhs, ExprKind::Var(s) if s.0 == "Float"));
}

#[test]
fn set_def_distinct_set_difference() {
    let (name, kind, _rhs) = parse_name_def("SafeDiv = distinct Int - {0}");
    assert_eq!(name, "SafeDiv");
    assert_eq!(kind, DefKind::Distinct);
}

#[test]
fn set_def_alias_named_set() {
    let (name, kind, rhs) = parse_name_def("MyNat = alias Nat");
    assert_eq!(name, "MyNat");
    assert_eq!(kind, DefKind::Alias);
    assert!(matches!(rhs, ExprKind::Var(s) if s.0 == "Nat"));
}

// ── Function parameter guards (`x for <expr>`) ─────────────────────────────────

#[test]
fn param_without_guard_has_none() {
    let items = parse_file("f : Int -> Int\nf(x) = x").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert!(def.params[0].guard.is_none());
}

#[test]
fn param_with_guard_parses_predicate() {
    let items = parse_file("sign : Int -> Int\nsign(x for x < 0) = -x").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_eq!(def.params[0].name.0, "x");
    let guard = def.params[0]
        .guard
        .as_ref()
        .unwrap_or_else(|| panic!("expected a guard on param `x`"));
    assert!(matches!(guard.kind, ExprKind::BinOp { op: BinOp::Lt, .. }));
}

#[test]
fn multi_param_guard_only_on_second_param() {
    let items = parse_file("f : Int * Int -> Int\nf(x, y for y > 0) = x + y").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert!(def.params[0].guard.is_none());
    assert!(def.params[1].guard.is_some());
}

// ── Literal-arm overloading (`f(0) = ...`) ──────────────────────────────────────

#[test]
fn literal_param_synthesizes_equality_guard() {
    let items = parse_file("factorial : Nat -> Nat\nfactorial(0) = 1").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_eq!(def.params.len(), 1);
    let guard = def.params[0]
        .guard
        .as_ref()
        .unwrap_or_else(|| panic!("expected a synthesized guard on the literal param"));
    assert!(matches!(guard.kind, ExprKind::BinOp { op: BinOp::Eq, .. }));
}

#[test]
fn two_literal_params_get_distinct_synthesized_names() {
    let items = parse_file("f : Int * Int -> Int\nf(0, 1) = 0").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_ne!(def.params[0].name.0, def.params[1].name.0);
}
