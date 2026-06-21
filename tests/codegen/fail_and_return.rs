use super::helpers::{jit_src_one_arg, jit_src_zero_arg};

const FAIL_SENTINEL: i64 = i64::MIN;

// ── `fail` literal and `fail expr` expressions ────────────────────────────────

/// A function returning bare `fail` emits FAIL_SENTINEL.
#[test]
fn fail_lit_returns_sentinel() {
    let src = r#"
main : -> Int | Fail
main() = fail
"#;
    assert_eq!(jit_src_zero_arg(src), FAIL_SENTINEL);
}

/// `fail 400` encodes as FAIL_SENTINEL + 401 (offset-encoded; distinguishable from success 400).
#[test]
fn fail_with_encodes_offset() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : Int -> Int
main(x) = fetch(x)
"#;
    // On success (x=1): raw value is 1.
    assert_eq!(jit_src_one_arg(src, 1), 1);
    // On failure (x=0): raw encoded value is FAIL_SENTINEL + 401.
    let encoded_400 = FAIL_SENTINEL.wrapping_add(401);
    assert_eq!(jit_src_one_arg(src, 0), encoded_400);
}

/// Success value 400 is NOT confused with `fail 400` — they are distinct i64 values.
#[test]
fn success_400_not_confused_with_fail_400() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : Int -> Int
main(x) = fetch(x)
"#;
    // fetch(400) returns success 400, not fail 400.
    assert_eq!(jit_src_one_arg(src, 400), 400);
    // fetch(0) returns fail 400, encoded as FAIL_SENTINEL + 401.
    assert_ne!(jit_src_one_arg(src, 0), 400);
}

// ── `?` on `!!` callees: success path ─────────────────────────────────────────

/// `?` on a `!!` callee passes the success value through unchanged.
#[test]
fn error_union_try_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : Int -> Int !! HTTPError
main(x) {
    result : Int = fetch(x)?
    result
}
"#;
    assert_eq!(jit_src_one_arg(src, 42), 42);
    assert_eq!(jit_src_one_arg(src, 1), 1);
}

/// `?` on a `!!` callee decodes `fail 400` → 400 and returns it.
#[test]
fn error_union_try_propagates_decoded_error() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : Int -> Int !! HTTPError
main(x) {
    result : Int = fetch(x)?
    result
}
"#;
    // x=0: fetch returns fail 400, ? decodes to 400 and main returns 400.
    assert_eq!(jit_src_one_arg(src, 0), 400);
}

/// `?` decodes `fail 503` → 503 correctly.
#[test]
fn error_union_try_propagates_503() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 503

main : Int -> Int !! HTTPError
main(x) {
    result : Int = fetch(x)?
    result
}
"#;
    assert_eq!(jit_src_one_arg(src, 0), 503);
    assert_eq!(jit_src_one_arg(src, 7), 7);
}

/// Chained `?` calls: first failure short-circuits.
#[test]
fn error_union_chained_try_first_fails() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Int !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : Int -> Int !! HTTPError
main(x) {
    a : Int = fetch(x)?
    b : Int = fetch(x + 1)?
    a + b
}
"#;
    // x=0: fetch(0) → fail 400, propagated immediately; b never called.
    assert_eq!(jit_src_one_arg(src, 0), 400);
    // x=5: fetch(5)=5, fetch(6)=6 → 11.
    assert_eq!(jit_src_one_arg(src, 5), 11);
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

/// `assert pred else fail expr` returns the encoded failure when pred is false.
#[test]
fn assert_else_fail_returns_encoded_error() {
    let src = r#"
HTTPError = {400, 503}

main : Int -> Int !! HTTPError
main(x) {
    assert x > 0 else fail 400
    x
}
"#;
    // x=5: assertion passes, returns 5.
    assert_eq!(jit_src_one_arg(src, 5), 5);
    // x=0: assertion fails, returns fail 400 → caller sees 400 after decode.
    // (In main the raw encoded value is returned; from outside the !! contract
    //  the encoded value propagates as-is since no outer ? is applied here.)
    let encoded_400 = FAIL_SENTINEL.wrapping_add(401);
    assert_eq!(jit_src_one_arg(src, 0), encoded_400);
}

/// Caller uses `?` to decode the `else fail` result.
#[test]
fn assert_else_fail_decoded_by_caller() {
    let src = r#"
HTTPError = {400, 503}

guard : Int -> Int !! HTTPError
guard(x) {
    assert x > 0 else fail 400
    x
}

main : Int -> Int !! HTTPError
main(x) {
    v : Int = guard(x)?
    v
}
"#;
    // x=7: guard passes, main returns 7.
    assert_eq!(jit_src_one_arg(src, 7), 7);
    // x=0: guard fails with fail 400, ? decodes to 400, main returns 400.
    assert_eq!(jit_src_one_arg(src, 0), 400);
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
