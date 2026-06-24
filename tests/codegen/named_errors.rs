use super::helpers::{jit_src_one_arg, jit_src_zero_arg_fallible};

// ── `!!` (error-union) propagation via `?` ───────────────────────────────────

/// On success `fetch` returns the input; `caller` propagates it unchanged.
#[test]
fn bang_bang_try_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(42)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(42));
}

/// On failure `fetch` returns `fail 400`; `?` propagates it as error code 400.
#[test]
fn bang_bang_try_error_propagated() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// Same for negative input.
#[test]
fn bang_bang_try_error_propagated_negative_input() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(0 - 5)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// Verify that 503 is propagated correctly.
#[test]
fn bang_bang_503_propagated() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 503

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(503));
}

/// Success path for 503-using function.
#[test]
fn bang_bang_503_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 503

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(10)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(10));
}

/// Two sequential `?` calls: if the first fails the error short-circuits.
#[test]
fn bang_bang_chained_try_first_fails() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Nat !! HTTPError
main() {
    a : Int = fetch(0)?
    b : Int = fetch(1)?
    a + b
}
"#;
    // fetch(0) = fail 400 → propagated immediately; b never called.
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// Two sequential `?` calls both succeed.
#[test]
fn bang_bang_chained_try_both_succeed() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : -> Nat !! HTTPError
main() {
    a : Int = fetch(5)?
    b : Int = fetch(6)?
    a + b
}
"#;
    // fetch(5) = 5, fetch(6) = 6, result = 11.
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(11));
}

/// Single-element error set.
#[test]
fn bang_bang_single_element_set_failure() {
    let src = r#"
NotFound = {404}

lookup : Int -> Nat !! NotFound
lookup(x) = if x > 0 then x else fail 404

main : -> Nat !! NotFound
main() {
    result : Int = lookup(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(404));
}

/// Single-element error set — success path.
#[test]
fn bang_bang_single_element_set_success() {
    let src = r#"
NotFound = {404}

lookup : Int -> Nat !! NotFound
lookup(x) = if x > 0 then x else fail 404

main : -> Nat !! NotFound
main() {
    result : Int = lookup(7)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(7));
}

/// `assert … else fail` clause: when the assertion fails the error propagates via `?`.
#[test]
fn bang_bang_assert_else_fail_propagates() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) {
    assert x > 0 else fail 400
    x
}

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(0)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Err(400));
}

/// Success path of `assert … else fail`.
#[test]
fn bang_bang_assert_else_fail_success() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) {
    assert x > 0 else fail 400
    x
}

main : -> Nat !! HTTPError
main() {
    result : Int = fetch(7)?
    result
}
"#;
    assert_eq!(jit_src_zero_arg_fallible(src), Ok(7));
}

// ── Named set membership in body (unrelated to `!!`) ─────────────────────────

/// Membership check on a named set in value position works correctly.
#[test]
fn named_set_membership_in_body() {
    let src = r#"
HTTPError = {400, 503}

main : Int -> Int
main(x) = if x in HTTPError then 1 else 0
"#;
    assert_eq!(jit_src_one_arg(src, 400), 1);
    assert_eq!(jit_src_one_arg(src, 503), 1);
    assert_eq!(jit_src_one_arg(src, 200), 0);
}
