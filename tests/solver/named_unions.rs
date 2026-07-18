//! Named union sets (pattern matching, step 3/4): `Shape = distinct (Circle:
//! Nat | Radius: NatPos)`, auto-generated per-arm constructors
//! (`Shape.Circle`, `Shape.Radius`), reusing the same `mk_D`/`from_D`
//! uninterpreted functions any ordinary single-basis `distinct` set gets
//! (`solver::preds::build_distinct_preds`) — v0 is Int-only, see
//! `semantics::elaborate::elaborate_name_def`'s labeled-arm Kind check.

use cantor::{error::CompileError, parser::parse_file, solver::check_file};

use super::helpers::*;

#[test]
fn named_union_constructor_call_proved() {
    proved_all(
        "Shape = distinct (Circle: Nat | Radius: NatPos)\n\
         describe : Shape -> Nat\n\
         describe(s) = from(s)\n\
         main : -> Nat\n\
         main() = describe(Shape.Circle(3)) + describe(Shape.Radius(4))",
    );
}

#[test]
fn named_union_constructor_basis_violation_is_counterexample() {
    // `Circle`'s own arm is `Nat` — a negative argument must fail the
    // basis obligation, exactly like an ordinary `litre(-1)` would today.
    counterexample(
        "Shape = distinct (Circle: Nat | Radius: NatPos)\n\
         bad : -> Shape\n\
         bad() = Shape.Circle(-1)",
    );
}

#[test]
fn named_union_tuple_arm_is_rejected_not_yet_implemented() {
    // v0 scope cut: every arm must be `Kind::Int` — a tuple arm hits
    // `distinct`'s hardcoded Int-only basis assumption
    // (`solver::preds::build_distinct_preds`) and must fail loudly with a
    // clear "not yet supported" error, never silently miscompile.
    let items = parse_file(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         main : -> Int\n\
         main() = 0",
    )
    .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Err(err) = check_file(&items, 60_000) else {
        panic!("expected elaboration to reject a tuple arm");
    };
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
    assert!(
        err.to_string().contains("named union arm"),
        "expected a clear message naming the unsupported arm shape: {err}"
    );
}

#[test]
fn named_union_unknown_label_is_undefined_function() {
    let items = parse_file(
        "Shape = distinct (Circle: Nat | Radius: NatPos)\n\
         main : -> Nat\n\
         main() = from(Shape.Square(3))",
    )
    .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Err(err) = check_file(&items, 60_000) else {
        panic!("expected an undefined-function error");
    };
    assert!(
        matches!(err, CompileError::UndefinedFunction { .. }),
        "expected UndefinedFunction, got {err:?}"
    );
}
