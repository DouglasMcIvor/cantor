//! Named union sets (pattern matching, step 3/4): `Shape = distinct (Circle:
//! Nat | Radius: NatPos)`, auto-generated per-arm constructors
//! (`Shape.Circle`, `Shape.Radius`), reusing the same `mk_D`/`from_D`
//! uninterpreted functions any ordinary single-basis `distinct` set gets
//! (`solver::preds::build_distinct_preds`) — every arm shares one Kind here
//! (`Kind::Int`), the case that needs no cross-kind tag/struct at all. See
//! `tests/solver/heterogeneous_named_unions.rs` for arms with genuinely
//! *different* Kinds from each other (`Circle: Nat | Rect: Nat * Nat`),
//! which does need one.

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

/// Found while prototyping constructor-pattern dispatch (deferred — see
/// backlog.md): a comprehension domain whose *source* is a `distinct`-sorted
/// set (rather than the Int-sorted sources every prior comprehension used)
/// was silently wrong in two independent places:
///
/// - `solver::sort::set_sort`'s `Comprehension` arm hardcoded
///   `tm.integer_sort()` for every comprehension's element sort, regardless
///   of its actual source — correct by coincidence for every Int-sourced
///   comprehension (guards, literal arms) but wrong for a `Shape`-sourced
///   one, where it silently produced a sort mismatch reported as "unsupported
///   domain set expression" rather than the real cause.
/// - `solver::membership::encode_comp_expr` (a comprehension filter's own
///   expression encoder) had no `Call` support at all, so `from(x)` — the
///   *only* way to get an Int-sorted term back out of a distinct-sorted one
///   — couldn't appear in a filter either.
///
/// Both are fixed as general solver-level corrections (not tied to any
/// particular named-union feature): `set_sort` now delegates to the
/// source's own sort, and `encode_comp_expr` special-cases `from(x)`.
#[test]
fn comprehension_over_distinct_sorted_source_with_from_filter_proved() {
    proved_all(
        "Shape = distinct (Circle: Nat | Radius: NatPos)\n\
         f : {s for s in Shape if from(s) == 0} -> Nat\n\
         f(s) = 0",
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
