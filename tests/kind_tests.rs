use cantor::ast::{BinOp, DefKind, Expr, NameDef, NameDefs};
use cantor::codegen::wire::range_kind;
use cantor::kind::{Kind, set_kind};
use cantor::span::{Span, Symbol};

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
fn set_kind_of_float32() {
    assert_eq!(
        set_kind(&Expr::var("Float32"), &NameDefs::new()).unwrap(),
        Kind::Float32
    );
}

#[test]
fn set_kind_of_finite_float32_is_the_same_kind_as_float32() {
    // A value-range refinement of Float32 (excludes ±infinity32/nan32), not
    // a second sort — mirrors Nat/Int sharing Kind::Int.
    assert_eq!(
        set_kind(&Expr::var("FiniteFloat32"), &NameDefs::new()).unwrap(),
        Kind::Float32
    );
}

#[test]
fn set_kind_of_float32_literal() {
    assert_eq!(
        set_kind(&Expr::float32(2.5), &NameDefs::new()).unwrap(),
        Kind::Float32
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
// until range inference is available — see tests/parser/collections.rs.

// ── Definition-cycle backstop (src/recursion.rs) ──────────────────────────────
// `semantics::wellfounded` rejects cyclic set definitions before `set_kind`
// ever sees one, so these build the cyclic `NameDefs` by hand — exactly the
// state the compiler would be in if that check ever developed a hole again,
// which is precisely how a recursive `distinct` set once stack-overflowed the
// compiler (an abort, so not even assertable in a test).

fn cyclic_defs(kind: DefKind) -> NameDefs {
    // `A = A * A` under the requested DefKind, with no well-foundedness check
    // in front of it.
    let mut defs = NameDefs::new();
    let name = Symbol::new("A");
    defs.insert(
        name.clone(),
        NameDef {
            name,
            kind,
            ty: None,
            value: Expr::binop(BinOp::Mul, Expr::var("A"), Expr::var("A")),
            labels: None,
            span: Span::dummy(),
        },
    );
    defs
}

#[test]
fn cyclic_alias_definition_is_an_ice_not_a_stack_overflow() {
    let defs = cyclic_defs(DefKind::Alias);
    let err = set_kind(&Expr::var("A"), &defs).unwrap_err();
    assert!(err.is_ice(), "expected an Ice, got {err:?}");
    assert!(
        err.to_string().contains('A'),
        "the Ice must name the definition it was expanding: {err}"
    );
}

#[test]
fn cyclic_distinct_definition_is_an_ice_not_a_stack_overflow() {
    // The shape that actually regressed: `set_kind`'s `Var` arm routes
    // `DefKind::Distinct` through `kind::named_union_value_kind`, which
    // recurses into the basis just like the alias case above.
    let defs = cyclic_defs(DefKind::Distinct);
    let err = set_kind(&Expr::var("A"), &defs).unwrap_err();
    assert!(err.is_ice(), "expected an Ice, got {err:?}");
}

// ── `Kind::Function` — `Domain -> Range` (higher-order functions step 2) ────

#[test]
fn set_kind_of_simple_arrow() {
    let expr = Expr::binop(BinOp::Arrow, Expr::var("Int"), Expr::var("Nat"));
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Function(Box::new(Kind::Int), Box::new(Kind::Int))
    );
}

#[test]
fn set_kind_of_arrow_with_tuple_domain() {
    // (Int * Bool) -> Bool
    let domain = Expr::binop(BinOp::Mul, Expr::var("Int"), Expr::var("Bool"));
    let expr = Expr::binop(BinOp::Arrow, domain, Expr::var("Bool"));
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Function(
            Box::new(Kind::Tuple(vec![Kind::Int, Kind::Bool])),
            Box::new(Kind::Bool)
        )
    );
}

#[test]
fn set_kind_of_curried_arrow_right_associates() {
    // Int -> (Int -> Int)
    let inner = Expr::binop(BinOp::Arrow, Expr::var("Int"), Expr::var("Int"));
    let expr = Expr::binop(BinOp::Arrow, Expr::var("Int"), inner);
    assert_eq!(
        set_kind(&expr, &NameDefs::new()).unwrap(),
        Kind::Function(
            Box::new(Kind::Int),
            Box::new(Kind::Function(Box::new(Kind::Int), Box::new(Kind::Int)))
        )
    );
}
