use cantor::ast::{BinOp, Expr, NameDefs};
use cantor::codegen::wire::range_kind;
use cantor::kind::{Kind, SetElemKind, set_kind};
// TODO: add `array_elem_kind` to the import once the function is implemented.

#[test]
fn set_kind_of_set_int() {
    let expr = Expr::call("Set", vec![Expr::var("Int")]);
    assert_eq!(set_kind(&expr, &NameDefs::new()), Kind::Set(SetElemKind::Int));
}

#[test]
fn set_kind_of_set_bool() {
    let expr = Expr::call("Set", vec![Expr::var("Bool")]);
    assert_eq!(set_kind(&expr, &NameDefs::new()), Kind::Set(SetElemKind::Bool));
}

#[test]
fn set_kind_of_set_nat() {
    // Nat is a subset of Int — same runtime kind as Int.
    let expr = Expr::call("Set", vec![Expr::var("Nat")]);
    assert_eq!(set_kind(&expr, &NameDefs::new()), Kind::Set(SetElemKind::Int));
}

#[test]
fn range_kind_set_int_or_fail() {
    // `Set(Int) | Fail` — the presence of Fail produces the fallible struct wire type.
    // On success the i64 payload holds the set pointer; on failure flag=1, payload=0.
    let set_int = Expr::call("Set", vec![Expr::var("Int")]);
    let fail    = Expr::var("Fail");
    let union   = Expr::binop(BinOp::Union, set_int, fail);
    assert_eq!(range_kind(&union, &NameDefs::new()), Kind::Tuple(vec![Kind::Fail, Kind::Set(SetElemKind::Int)]));
}

// ── Homogeneous tuple literals `[...]` — kind checking ────────────────────────
// `array_elem_kind(elems)` returns the single shared Kind if all elements have
// the same kind, or an error if the literal is heterogeneous.
// TODO: remove #[cfg(any())] gates once cantor::kind::array_elem_kind is implemented.

#[cfg(any())]
#[test]
fn array_elem_kind_uniform_int() {
    // [1, 2, 3] — all Int-kinded.
    let elems = vec![Expr::int(1), Expr::int(2), Expr::int(3)];
    assert_eq!(array_elem_kind(&elems), Ok(Kind::Int));
}

#[cfg(any())]
#[test]
fn array_elem_kind_uniform_bool() {
    // [true, false] — all Bool-kinded.
    let elems = vec![Expr::bool(true), Expr::bool(false)];
    assert_eq!(array_elem_kind(&elems), Ok(Kind::Bool));
}

#[cfg(any())]
#[test]
fn array_elem_kind_empty_is_ok() {
    // [] has no elements, so the check trivially passes.
    // The kind is unresolved / Bottom; implementation may return a special value.
    assert!(array_elem_kind(&[]).is_ok());
}

#[cfg(any())]
#[test]
fn array_elem_kind_int_then_bool_is_error() {
    // [1, 2, true] — Int followed by Bool → kind mismatch.
    let elems = vec![Expr::int(1), Expr::int(2), Expr::bool(true)];
    assert!(array_elem_kind(&elems).is_err(),
        "expected kind error for [1, 2, true]");
}

#[cfg(any())]
#[test]
fn array_elem_kind_bool_then_int_is_error() {
    // [true, 1] — Bool followed by Int → kind mismatch.
    let elems = vec![Expr::bool(true), Expr::int(1)];
    assert!(array_elem_kind(&elems).is_err(),
        "expected kind error for [true, 1]");
}

#[cfg(any())]
#[test]
fn array_elem_kind_single_element() {
    // [42] — single Int element; trivially homogeneous.
    let elems = vec![Expr::int(42)];
    assert_eq!(array_elem_kind(&elems), Ok(Kind::Int));
}
