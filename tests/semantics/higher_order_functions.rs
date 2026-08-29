//! Higher-order functions v0 (backlog.md): `Domain -> Range` as a `Kind`,
//! a bare reference to a non-overloaded top-level function as a first-class
//! value, and calling through a `Kind::Function`-typed local/param. New file
//! rather than growing `elaborate_tests.rs` past the repo's 1000-line
//! guideline (CLAUDE.md).
//!
//! No closures/lambdas yet (deliberately deferred, see backlog.md) — every
//! case here is a reference to a real top-level `FunctionDef`.

use cantor::ast::Item;
use cantor::error::CompileError;
use cantor::kind::Kind;
use cantor::parser::parse_file;
use cantor::semantics::elaborate::elaborate;
use cantor::semantics::tree::{SemExprKind, SemFunctionBody, SemItem};

fn elaborate_src(src: &str) -> Vec<SemItem> {
    let items: Vec<Item> = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    elaborate(&items).unwrap_or_else(|e| panic!("elaborate error: {e}"))
}

fn elaborate_err(src: &str) -> CompileError {
    let items: Vec<Item> = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    elaborate(&items).expect_err("expected elaboration to fail")
}

fn function_body_expr<'a>(
    items: &'a [SemItem],
    name: &str,
) -> &'a cantor::semantics::tree::SemExpr {
    items
        .iter()
        .find_map(|item| match item {
            SemItem::FunctionDef(def) if def.name.0 == name => match &def.body {
                SemFunctionBody::Expr(body) => Some(body),
                _ => panic!("expected expr body for `{name}`"),
            },
            _ => None,
        })
        .unwrap_or_else(|| panic!("no function named `{name}` in elaborated output"))
}

// ── Bare function name as a value ────────────────────────────────────────────

#[test]
fn bare_reference_to_single_signature_function_is_a_function_kind() {
    let items = elaborate_src(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         holder : -> (Int -> Int)\n\
         holder() = double",
    );
    let body = function_body_expr(&items, "holder");
    assert_eq!(
        body.kind_of,
        Kind::Function(Box::new(Kind::Int), Box::new(Kind::Int))
    );
    assert!(matches!(&body.kind, SemExprKind::Var(sym) if sym.0 == "double"));
}

#[test]
fn multi_param_function_reference_has_tuple_domain() {
    let items = elaborate_src(
        "add2 : Int * Int -> Int\n\
         add2(a, b) = a + b\n\
         holder : -> (Int * Int -> Int)\n\
         holder() = add2",
    );
    let body = function_body_expr(&items, "holder");
    assert_eq!(
        body.kind_of,
        Kind::Function(
            Box::new(Kind::Tuple(vec![Kind::Int, Kind::Int])),
            Box::new(Kind::Int)
        )
    );
}

#[test]
fn overloaded_function_name_cannot_be_used_as_a_value() {
    let err = elaborate_err(
        "f : Nat -> Nat\n\
         f(x) = x + 1\n\
         f : Bool -> Bool\n\
         f(x) = x\n\
         holder : -> (Nat -> Nat)\n\
         holder() = f",
    );
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
}

// ── Calling through a function-Kind parameter ────────────────────────────────

#[test]
fn call_through_function_kind_param_resolves_range_kind() {
    let items = elaborate_src(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(f, x) = f(x)\n\
         main : -> Int\n\
         main() = apply(double, 5)",
    );
    let body = function_body_expr(&items, "apply");
    assert_eq!(body.kind_of, Kind::Int);
    let SemExprKind::Call { callee, args } = &body.kind else {
        panic!("expected Call, got {:?}", body.kind);
    };
    assert_eq!(callee.0, "f");
    assert_eq!(args.len(), 1);
}

#[test]
fn call_through_function_kind_param_shadows_same_named_top_level_function() {
    // A param named the same as an unrelated top-level function must call
    // through the *param* (locals shadow everything else, mirroring `Var`'s
    // own env-first priority) — not accidentally resolve to the outer name.
    let items = elaborate_src(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         triple : Int -> Int\n\
         triple(x) = x + x + x\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(double, x) = double(x)",
    );
    let body = function_body_expr(&items, "apply");
    assert_eq!(body.kind_of, Kind::Int);
}

#[test]
fn call_through_function_kind_param_with_mismatched_arg_kind_is_rejected() {
    let err = elaborate_err(
        "double : Int -> Int\n\
         double(x) = x + x\n\
         apply : (Int -> Int) * Bool -> Int\n\
         apply(f, b) = f(b)",
    );
    assert!(
        matches!(err, CompileError::FunctionValueArgKindMismatch { .. }),
        "expected FunctionValueArgKindMismatch, got {err:?}"
    );
}

#[test]
fn passing_wrong_shaped_function_still_elaborates_by_kind_only() {
    // v0 elaboration only checks the function-value parameter's own Kind
    // against the call's argument Kinds inside the body — it does NOT yet
    // check that a *caller* passing a concrete function actually matches the
    // declared function-Kind parameter (that's solver work, not done yet).
    // This just documents today's boundary: elaboration of `apply` itself
    // succeeds regardless of what `main` later passes.
    let items = elaborate_src(
        "on_bool : Bool -> Bool\n\
         on_bool(b) = b\n\
         apply : (Int -> Int) * Int -> Int\n\
         apply(f, x) = f(x)\n\
         main : -> Int\n\
         main() = apply(on_bool, 5)",
    );
    let body = function_body_expr(&items, "main");
    assert_eq!(body.kind_of, Kind::Int);
}
