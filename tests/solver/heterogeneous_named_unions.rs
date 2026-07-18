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
//! Arms are *not* required to have pairwise-distinct Kinds — a v0 scope cut
//! this file used to enforce (`Circle: Nat | Square: NatPos | Rect: Nat *
//! Nat`, two `Int`-Kind arms mixed with a `Tuple`-Kind one, was rejected)
//! has since been lifted: the underlying constructor-naming/dispatch gaps in
//! the general cross-kind union machinery are fixed —
//! `solver::encode_call::coerce_arg_to_labeled_arm` selects a labeled
//! constructor's arm by its known position rather than searching by CVC5
//! sort (which silently collapsed same-Kind labeled arms onto the same
//! constructor — confirmed as real solver-level unsoundness,
//! `Shape.Circle(5)` and `Shape.Square(5)` provably "equal", see
//! `heterogeneous_arm_same_kind_labels_stay_distinct_proved` below),
//! `solver::membership_seq::membership_constraint_for_dt` matches by
//! position instead of by name, and `kind::named_union_value_kind` reports
//! one Kind per syntactic label instead of the whole union's Kind-deduped
//! arm list (codegen's `Compiler::named_union_arms` table).

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
fn heterogeneous_arm_duplicate_kind_arms_proved() {
    // `Circle: Nat` and `Square: NatPos` share `Kind::Int`, mixed with
    // `Rect: Nat * Nat` (`Kind::Tuple`) — used to be rejected by the
    // pairwise-distinctness v0 scope cut (see module doc comment); now
    // accepted and proved like any other arm combination.
    proved_all(
        "Shape = distinct (Circle: Nat | Square: NatPos | Rect: Nat * Nat)\n\
         make_circle : Nat -> Shape\n\
         make_circle(n) = Shape.Circle(n)\n\
         make_square : NatPos -> Shape\n\
         make_square(n) = Shape.Square(n)\n\
         make_rect : Nat * Nat -> Shape\n\
         make_rect(p) = Shape.Rect(p)\n\
         main : -> Shape\n\
         main() = make_square(3)",
    );
}

#[test]
fn heterogeneous_arm_same_kind_labels_stay_distinct_proved() {
    // The core soundness regression guard: `Circle` and `Square` share
    // `Kind::Int`, but constructing through different labels must still
    // produce provably *different* values — before the fix,
    // `coerce_to_union_dt` picked a union-DT constructor by matching CVC5
    // *sort* rather than by label, so any two same-Kind labeled arms
    // collapsed onto the same physical constructor and this assertion was
    // wrongly reported "always fails".
    proved(
        "Shape = distinct (Circle: Nat | Square: NatPos | Rect: Nat * Nat)\n\
         main : -> Int\n\
         main() {\n\
             assert Shape.Circle(5) != Shape.Square(5)\n\
             0\n\
         }",
    );
}

#[test]
fn heterogeneous_arm_second_same_kind_label_basis_obligation_checked() {
    // `Square`'s own arm is `NatPos` (>= 1), the *second* of two same-Kind
    // (`Int`) labeled arms — regression guard for a bug found while fixing
    // the above: checking the basis obligation against the already-wrapped
    // (union-DT) argument, instead of the raw pre-coercion one, tested the
    // wrong arm's tester whenever a labeled arm wasn't at DT position 0,
    // wrongly rejecting `Shape.Square(1)` (1 *is* in `NatPos`).
    counterexample(
        "Shape = distinct (Circle: Nat | Square: NatPos | Rect: Nat * Nat)\n\
         bad : -> Shape\n\
         bad() = Shape.Square(0)",
    );
    proved(
        "Shape = distinct (Circle: Nat | Square: NatPos | Rect: Nat * Nat)\n\
         ok : -> Shape\n\
         ok() = Shape.Square(1)",
    );
}
