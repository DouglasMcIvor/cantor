use cantor::ast::{BinOp, Expr, NameDefs};
use cantor::codegen::wire::range_kind;
use cantor::kind::{Kind, SetElemKind, set_kind};

#[test]
fn set_kind_of_set_int() {
    let expr = Expr::call("Set", vec![Expr::var("Int")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(SetElemKind::Int)
    );
}

#[test]
fn set_kind_of_set_bool() {
    let expr = Expr::call("Set", vec![Expr::var("Bool")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(SetElemKind::Bool)
    );
}

#[test]
fn set_kind_of_set_nat() {
    // Nat is a subset of Int — same runtime kind as Int.
    let expr = Expr::call("Set", vec![Expr::var("Nat")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(SetElemKind::Int)
    );
}

#[test]
fn range_kind_set_int_or_fail() {
    // `Set(Int) | Fail` — the presence of Fail produces the fallible struct wire type.
    // On success the i64 payload holds the set pointer; on failure flag=1, payload=0.
    let set_int = Expr::call("Set", vec![Expr::var("Int")]);
    let fail = Expr::var("Fail");
    let union = Expr::binop(BinOp::Union, set_int, fail);
    assert_eq!(
        range_kind(&union, &NameDefs::new()).unwrap(),
        Kind::Tuple(vec![Kind::Fail, Kind::Set(SetElemKind::Int)])
    );
}

// ── Homogeneous tuple literals `[...]` — kind checking ────────────────────────
// Enforcing that `[a, b, c]` elements all belong to the same set is deferred
// until range inference is available — see tests/parser_tests.rs.
