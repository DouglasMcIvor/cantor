use super::helpers::{Propagation, jit_src_zero_arg_propagation};

// ── `none` literal and the `{tag=2, i64=0}` wire shape ──────────────────────

#[test]
fn none_lit_causes_propagation() {
    let src = r#"
main : -> Int | None
main() = none
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::None);
}

#[test]
fn none_success_path() {
    let src = r#"
lookup : Int -> Int | None
lookup(x) = if x > 0 then x else none

main : -> Int | None
main() = lookup(5)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::Success(5));
}

#[test]
fn none_failure_path() {
    let src = r#"
lookup : Int -> Int | None
lookup(x) = if x > 0 then x else none

main : -> Int | None
main() = lookup(-5)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::None);
}

// ── `?` propagation of `None` ────────────────────────────────────────────────

#[test]
fn try_propagates_none_success_path() {
    let src = r#"
lookup : Int -> Int | None
lookup(x) = if x > 0 then x else none

caller : Int -> Int | None
caller(x) = lookup(x)? + 1

main : -> Int | None
main() = caller(5)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::Success(6));
}

#[test]
fn try_propagates_none_failure_path() {
    let src = r#"
lookup : Int -> Int | None
lookup(x) = if x > 0 then x else none

caller : Int -> Int | None
caller(x) = lookup(x)? + 1

main : -> Int | None
main() = caller(-5)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::None);
}

// ── Full coexistence: `T | Fail | None` ─────────────────────────────────────
//
// The three outcomes (success, Fail, None) all share one `{tag, i64}` LLVM
// wire shape — `tag` is 0/1/2 respectively (`codegen::Compiler::TAG_*`).

#[test]
fn fail_and_none_coexist_success_path() {
    let src = r#"
classify : Int -> Int | Fail | None
classify(x) {
    assert x != 0
    if x > 0 then x else none
}

main : -> Int | Fail | None
main() = classify(5)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::Success(5));
}

#[test]
fn fail_and_none_coexist_none_path() {
    let src = r#"
classify : Int -> Int | Fail | None
classify(x) {
    assert x != 0
    if x > 0 then x else none
}

main : -> Int | Fail | None
main() = classify(-5)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::None);
}

#[test]
fn fail_and_none_coexist_fail_path() {
    let src = r#"
classify : Int -> Int | Fail | None
classify(x) {
    assert x != 0
    if x > 0 then x else none
}

main : -> Int | Fail | None
main() = classify(0)
"#;
    assert_eq!(jit_src_zero_arg_propagation(src), Propagation::Fail(0));
}
