use super::helpers::{jit_src_one_arg, jit_src_zero_arg, jit_src_zero_arg_fallible};

// ── `fail` literal and `fail expr` expressions ────────────────────────────────

/// A zero-arg function returning bare `fail` returns a failure struct (flag=1, code=0).
#[test]
fn fail_lit_causes_failure() {
    let src = r#"
main : -> Int | Fail
main() = fail
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(0));
}

/// `fail 400` causes a failure with error code 400.
#[test]
fn fail_with_carries_error_code() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    result : Int = fetch(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// Success path: `fail 400` is not emitted when the predicate holds.
#[test]
fn fail_with_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    result : Int = fetch(1)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(1));
}

/// Success value 400 is NOT confused with `fail 400` — the flag bit distinguishes them.
#[test]
fn success_400_not_confused_with_fail_400() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    result : Int = fetch(400)?
    result
}
"#;
    // fetch(400) returns success 400 (flag=0, payload=400).
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(400));
}

// ── `?` on `!!` callees: success path ─────────────────────────────────────────

/// `?` on a `!!` callee passes the success value through unchanged.
#[test]
fn error_union_try_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    result : Int = fetch(42)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(42));
}

/// `?` on a `!!` callee propagates `fail 400` as an error with code 400.
#[test]
fn error_union_try_propagates_error() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    result : Int = fetch(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// `?` propagates `fail 503` with the correct error code.
#[test]
fn error_union_try_propagates_503() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 503

main : -> Int !! HTTPError
main() {
    result : Int = fetch(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(503));
}

/// Chained `?` calls: first failure short-circuits before the second call.
#[test]
fn error_union_chained_try_first_fails() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    a : Int = fetch(0)?
    b : Int = fetch(1)?
    a + b
}
"#;
    // fetch(0) fails; b is never evaluated.
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// Chained `?` calls succeed when all callees succeed.
#[test]
fn error_union_chained_try_both_succeed() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Int !! HTTPError
main() {
    a : Int = fetch(5)?
    b : Int = fetch(6)?
    a + b
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(11));
}

// ── `return` statement ────────────────────────────────────────────────────────

/// `return expr` causes early exit from a block body.
#[test]
fn return_stmt_early_exit() {
    let src = r#"
main : Int -> Int
main(x) {
    return x * 2
    99
}
"#;
    // Should return x*2, not 99.
    assert_eq!(jit_src_one_arg(src, 5), 10);
    assert_eq!(jit_src_one_arg(src, 0), 0);
}

/// Conditional early `return` using if-then-else in statement position.
#[test]
fn return_stmt_conditional() {
    let src = r#"
main : Int -> Int
main(x) {
    y : Int = if x > 0 then x else 0 - x
    return y
    0
}
"#;
    assert_eq!(jit_src_one_arg(src, 5), 5);
    assert_eq!(jit_src_one_arg(src, -3), 3);
}

// ── `assert … else fail expr` ────────────────────────────────────────────────

/// `assert pred else fail expr` causes failure with the given code when pred is false.
#[test]
fn assert_else_fail_causes_failure() {
    let src = r#"
HTTPError = {400, 503}

main : -> Int !! HTTPError
main() {
    assert 0 > 0 else fail 400
    42
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// `assert pred else fail expr` succeeds normally when pred is true.
#[test]
fn assert_else_fail_success_path() {
    let src = r#"
HTTPError = {400, 503}

main : -> Int !! HTTPError
main() {
    assert 1 > 0 else fail 400
    42
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(42));
}

/// Caller uses `?` to propagate the `else fail` failure.
#[test]
fn assert_else_fail_propagated_by_try() {
    let src = r#"
HTTPError = {400, 503}

guard : Int -> Int !! HTTPError
guard(x) {
    assert x > 0 else fail 400
    x
}

main : -> Int !! HTTPError
main() {
    v : Int = guard(0)?
    v
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// `assert pred else fail` success path passes through the result.
#[test]
fn assert_else_fail_caller_success() {
    let src = r#"
HTTPError = {400, 503}

guard : Int -> Int !! HTTPError
guard(x) {
    assert x > 0 else fail 400
    x
}

main : -> Int !! HTTPError
main() {
    v : Int = guard(7)?
    v
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(7));
}

// ── `assert … else return expr` ──────────────────────────────────────────────

/// `assert pred else return expr` returns `expr` directly when pred is false.
#[test]
fn assert_else_return_direct_value() {
    let src = r#"
main : Int -> Int
main(x) {
    assert x > 0 else return 0 - 1
    x * 2
}
"#;
    // x=5: assertion passes, returns 10.
    assert_eq!(jit_src_one_arg(src, 5), 10);
    // x=0: assertion fails, returns -1 directly.
    assert_eq!(jit_src_one_arg(src, 0), -1);
}

// ── zero-arg helpers (non-fallible) ──────────────────────────────────────────

/// Basic zero-arg smoke test (non-fallible).
#[test]
fn zero_arg_constant_return() {
    let src = r#"
main : -> Int
main() = 42
"#;
    assert_eq!(jit_src_zero_arg(src), 42);
}
