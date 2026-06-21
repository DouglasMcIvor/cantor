use cantor::ast::{BinOp, Expr};
use cantor::kind::{Kind, SetElemKind, range_kind, set_kind};

#[test]
fn set_kind_of_set_int() {
    let expr = Expr::call("Set", vec![Expr::var("Int")]);
    assert_eq!(set_kind(&expr), Kind::Set(SetElemKind::Int));
}

#[test]
fn set_kind_of_set_bool() {
    let expr = Expr::call("Set", vec![Expr::var("Bool")]);
    assert_eq!(set_kind(&expr), Kind::Set(SetElemKind::Bool));
}

#[test]
fn set_kind_of_set_nat() {
    // Nat is a subset of Int — same runtime kind as Int.
    let expr = Expr::call("Set", vec![Expr::var("Nat")]);
    assert_eq!(set_kind(&expr), Kind::Set(SetElemKind::Int));
}

#[test]
fn range_kind_set_int_or_fail() {
    // `Set(Int) | Fail` — the Fail branch must not clobber the Set kind.
    let set_int = Expr::call("Set", vec![Expr::var("Int")]);
    let fail    = Expr::var("Fail");
    let union   = Expr::binop(BinOp::Union, set_int, fail);
    assert_eq!(range_kind(&union), Kind::Set(SetElemKind::Int));
}
