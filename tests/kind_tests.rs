use cantor::ast::{BinOp, Expr, NameDefs};
use cantor::codegen::wire::range_kind;
use cantor::kind::{Kind, set_kind};

#[test]
fn set_kind_of_set_int() {
    let expr = Expr::call("Set", vec![Expr::var("Int")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(Box::new(Kind::Int))
    );
}

#[test]
fn set_kind_of_set_bool() {
    let expr = Expr::call("Set", vec![Expr::var("Bool")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(Box::new(Kind::Bool))
    );
}

#[test]
fn set_kind_of_set_nat() {
    // Nat is a subset of Int — same runtime kind as Int.
    let expr = Expr::call("Set", vec![Expr::var("Nat")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(Box::new(Kind::Int))
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
        Kind::Tuple(vec![Kind::Fail, Kind::Set(Box::new(Kind::Int))])
    );
}

// ── `SetElemKind` elimination: `Kind::Set` now nests any scalar `Kind` ───────
// Regression tests for replacing the old `SetElemKind { Int, Bool }` enum
// with `Kind::Set(Box<Kind>)`. `Int`/`Bool` behavior above is unchanged;
// these cover the two things that actually changed: `Fail` is now a legal
// scalar element kind, and a genuinely unsupported element kind (anything
// that isn't a single raw i64 word) reports a clean `CompileError` instead
// of `unreachable!()`-panicking.

#[test]
fn set_kind_of_set_fail() {
    let expr = Expr::call("Set", vec![Expr::var("Fail")]);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Set(Box::new(Kind::Fail))
    );
}

#[test]
fn set_kind_of_set_tuple_is_unsupported_not_a_panic() {
    // `Set(Int * Int)` — a Tuple element kind needs structural equality/
    // ordering the compiler doesn't implement yet (see kind::is_scalar_word_kind).
    let tuple = Expr::binop(BinOp::Mul, Expr::var("Int"), Expr::var("Int"));
    let expr = Expr::call("Set", vec![tuple]);
    let err = set_kind(&expr, &NameDefs::new()).unwrap_err();
    assert!(
        matches!(err, cantor::error::CompileError::Unsupported { .. }),
        "expected CompileError::Unsupported, got {err:?}"
    );
}

// ── Homogeneous tuple literals `[...]` — kind checking ────────────────────────
// Enforcing that `[a, b, c]` elements all belong to the same set is deferred
// until range inference is available — see tests/parser_tests.rs.
