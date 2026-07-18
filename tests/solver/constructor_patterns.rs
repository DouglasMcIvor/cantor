//! Constructor patterns (pattern-matching plan, step 4/4):
//! `size(Tree.leaf2(x, y)) = ...` — matching a function parameter against a
//! labeled named-union arm, destructuring the arm's own payload into fresh
//! binder names for the body. Desugars at elaboration time
//! (`semantics::elaborate::desugar_param_patterns`/
//! `build_ctor_pattern_prelude`) into a domain-narrowing comprehension
//! (using a synthesized `{Union}.{Label}?` tester call) plus a body-prelude
//! `let`/destructuring `let` (using a synthesized `{Union}.{Label}!`
//! extractor call) — no new `SemExprKind` on either side.
//!
//! v0 scope: non-recursive named unions only (recursive sets aren't
//! implemented past the well-foundedness check, see backlog.md).

use cantor::{error::CompileError, parser::parse_file, solver::check_file};

use super::helpers::*;

#[test]
fn scalar_ctor_pattern_arm_proved() {
    proved_all(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         area : Shape -> Nat\n\
         area(Shape.Circle(r)) = r * r\n\
         area : Shape -> Nat\n\
         area(Shape.Rect(x, y)) = x * y\n\
         main : -> Nat\n\
         main() = area(Shape.Circle(3)) + area(Shape.Rect((4, 5)))",
    );
}

#[test]
fn tuple_ctor_pattern_arm_destructures_both_elements_proved() {
    proved_all(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         area : Shape -> Nat\n\
         area(Shape.Circle(r)) = r * r\n\
         area : Shape -> Nat\n\
         area(Shape.Rect(x, y)) = x * y\n\
         main : -> Nat\n\
         main() = area(Shape.Rect((4, 5)))",
    );
}

#[test]
fn ctor_pattern_arm_disjointness_proved() {
    // The overload-disjointness obligation between the two `area` arms —
    // regression guard for `solver::disjointness::fresh_overload_param_terms`'s
    // `TaggedUnion` case (previously `Unknown`, "non-scalar parameter
    // positions are not yet supported").
    let results = check_all(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         area : Shape -> Nat\n\
         area(Shape.Circle(r)) = r * r\n\
         area : Shape -> Nat\n\
         area(Shape.Rect(x, y)) = x * y\n\
         main : -> Nat\n\
         main() = area(Shape.Circle(3))",
    );
    // `check_overload_disjointness` pushes its own `("area", [...])` entry
    // alongside the ordinary per-signature one (same top-level name), so
    // this searches every group's sig results rather than assuming the
    // first `area` entry is the disjointness one.
    let (label, result) = results
        .iter()
        .flat_map(|(_, sig_results)| sig_results)
        .find(|(label, _)| label.contains("disjointness"))
        .unwrap_or_else(|| panic!("expected a disjointness obligation, got {results:?}"));
    assert_eq!(
        result,
        &CheckResult::Proved,
        "expected `{label}` to be Proved, got {result:?}"
    );
}

#[test]
fn ctor_pattern_arm_out_of_basis_payload_is_counterexample() {
    // `-r ∈ Nat` only holds when `r == 0` — the domain-narrowing filter must
    // actually constrain the extracted payload to `Circle`'s own basis
    // (`Nat`, i.e. `r >= 0`), not just test the tag; if it didn't, `r` would
    // be an unconstrained free variable and this would be falsely proved.
    counterexample(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         bad : Shape -> Nat\n\
         bad(Shape.Circle(r)) = -r",
    );
}

#[test]
fn ctor_pattern_unknown_label_is_undefined_function() {
    let items = parse_file(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         area : Shape -> Nat\n\
         area(Shape.Square(r)) = r * r",
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
fn ctor_pattern_arity_mismatch_is_unsupported() {
    let items = parse_file(
        "Shape = distinct (Circle: Nat | Rect: Nat * Nat)\n\
         area : Shape -> Nat\n\
         area(Shape.Rect(x)) = x * x",
    )
    .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Err(err) = check_file(&items, 60_000) else {
        panic!("expected an arity-mismatch error");
    };
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
}
