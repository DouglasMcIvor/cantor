//! Named unions whose arms have genuinely *different* Kinds from each other
//! (`Shape = distinct (Circle: Nat | Rect: Nat * Nat)`) — the generalization
//! beyond `tests/solver/named_unions.rs`'s same-Kind-arm case, and the
//! explicit next step recorded in backlog.md after `distinct`'s basis
//! generalization (`tests/solver/distinct_basis.rs`).
//!
//! `Shape` itself becomes a real tagged union at both layers: a cross-kind
//! CVC5 datatype (`solver::sort::build_union_datatype_sort`, already
//! generic) at the solver layer, and the `{ i32 tag, i64 leaves }` struct
//! (`codegen::coerce::build_tagged_union_value`, already used for ordinary
//! `A | B` coercion) at the codegen layer — `Shape.Circle(r)`/`Shape.Rect(p)`
//! are the one genuinely new piece on each side (wrapping the argument into
//! the union DT's matching arm constructor before `mk_Shape`, and building
//! the tagged struct instead of the same-Kind case's pure passthrough).
//!
//! v0 scope: every arm's Kind must be *pairwise distinct* from every other
//! arm's Kind (`semantics::elaborate::validate_distinct_basis`) — sidesteps
//! a pre-existing constructor-naming collision in the general cross-kind
//! union machinery when two arms share a Kind (found while implementing
//! this, tracked separately in backlog.md, not fixed here).

use cantor::{error::CompileError, parser::parse_file, solver::check_file};

use super::helpers::*;

#[test]
fn heterogeneous_arm_constructor_basis_violation_int_arm_is_counterexample() {
    // `Circle`'s own arm is `Nat` — a negative argument must fail the basis
    // obligation, exactly like an ordinary `litre(-1)` would.
    counterexample(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         bad : -> Shape\n\
         bad() = Shape.Circle(-1)",
    );
}

#[test]
fn heterogeneous_arm_constructor_basis_violation_tuple_arm_is_counterexample() {
    // `Rect`'s own arm is `Nat * Nat` — a negative tuple element must fail
    // the basis obligation the same way.
    counterexample(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         bad : -> Shape\n\
         bad() = Shape.Rect((3, -1))",
    );
}

#[test]
fn heterogeneous_arm_constructor_valid_args_proved() {
    proved_all(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         make_circle : Nat -> Shape\n\
         make_circle(n) = Shape.Circle(n)\n\
         make_rect : Nat * Nat -> Shape\n\
         make_rect(p) = Shape.Rect(p)\n\
         main : -> Shape\n\
         main() = make_rect((3, 4))",
    );
}

#[test]
fn heterogeneous_arm_three_arms_including_bool_proved() {
    // Three pairwise-distinct-Kind arms (Int, Tuple, Bool) — broader
    // coverage than the two-arm case above, confirms the arm-index/tag
    // wiring generalizes past two arms.
    proved_all(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat | Flag: Bool)\n\
         make_flag : Bool -> Shape\n\
         make_flag(b) = Shape.Flag(b)\n\
         main : -> Shape\n\
         main() = make_flag(true)",
    );
}

#[test]
fn heterogeneous_arm_unknown_label_is_undefined_function() {
    let items = parse_file(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
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

#[test]
fn heterogeneous_arm_unlabeled_is_rejected_not_yet_implemented() {
    // No labels at all — there's no way to pick "which arm" a constructor
    // argument belongs to, so this must be rejected loudly, not silently
    // reach the solver with an ambiguous basis.
    let items = parse_file(
        "Shape = distinct (Nat | Nat * Nat)\n\
         main : -> Int\n\
         main() = 0",
    )
    .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Err(err) = check_file(&items, 60_000) else {
        panic!("expected elaboration to reject an unlabeled heterogeneous union");
    };
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
    assert!(
        err.to_string().contains("unlabeled"),
        "expected a message naming the missing labels: {err}"
    );
}

#[test]
fn heterogeneous_arm_duplicate_kind_arms_rejected_not_yet_implemented() {
    // `Circle: Nat` and `Square: NatPos` share `Kind::Int`, mixed with
    // `Rect: Nat * Nat` (`Kind::Tuple`) — the pairwise-distinctness v0 scope
    // cut (see module doc comment) must reject this loudly rather than
    // silently reaching `build_union_datatype_sort`'s constructor-naming
    // collision.
    let items = parse_file(
        "Shape = distinct (Circle: Nat | Square: NatPos | Rect: Nat * Nat)\n\
         main : -> Int\n\
         main() = 0",
    )
    .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Err(err) = check_file(&items, 60_000) else {
        panic!("expected elaboration to reject two arms sharing a Kind");
    };
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
    assert!(
        err.to_string().contains("sharing kind"),
        "expected a message naming the duplicate-Kind arms: {err}"
    );
}
