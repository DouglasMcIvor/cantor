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
