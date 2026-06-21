use super::helpers::jit_src_one_arg;

// ── `!!` (error-union) propagation via `?` ───────────────────────────────────

/// On success `fetch` returns the input; `caller` propagates it unchanged.
#[test]
fn bang_bang_try_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

caller : Int -> Nat !! HTTPError
caller(x) {
    result : Int = fetch(x)?
    result
}

main : Int -> Int
main(x) = caller(x)
"#;
    assert_eq!(jit_src_one_arg(src, 42), 42);
    assert_eq!(jit_src_one_arg(src, 1), 1);
}

/// On failure (x <= 0) `fetch` returns `fail 400`; `?` decodes it to 400 and
/// propagates it up through `caller` and then `main`.
#[test]
fn bang_bang_try_error_propagated() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

caller : Int -> Nat !! HTTPError
caller(x) {
    result : Int = fetch(x)?
    result
}

main : Int -> Int
main(x) = caller(x)
"#;
    assert_eq!(jit_src_one_arg(src, 0), 400);
    assert_eq!(jit_src_one_arg(src, -5), 400);
}

/// Verify that 503 is decoded and propagated correctly.
#[test]
fn bang_bang_503_propagated() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 503

main : Int -> Nat !! HTTPError
main(x) {
    result : Int = fetch(x)?
    result
}
"#;
    assert_eq!(jit_src_one_arg(src, 0), 503);
    assert_eq!(jit_src_one_arg(src, 10), 10);
}

/// Two sequential `?` calls: if the first fails the error short-circuits before
/// the second call is evaluated.
#[test]
fn bang_bang_chained_try_first_fails() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

main : Int -> Nat !! HTTPError
main(x) {
    a : Int = fetch(x)?
    b : Int = fetch(x + 1)?
    a + b
}
"#;
    // x = 0: fetch(0) = fail 400 → decoded to 400, returned immediately.
    assert_eq!(jit_src_one_arg(src, 0), 400);
    // x = 5: fetch(5) = 5, fetch(6) = 6, result = 11.
    assert_eq!(jit_src_one_arg(src, 5), 11);
}

/// Single-element error set.
#[test]
fn bang_bang_single_element_set() {
    let src = r#"
NotFound = {404}

lookup : Int -> Nat !! NotFound
lookup(x) = if x > 0 then x else fail 404

main : Int -> Nat !! NotFound
main(x) {
    result : Int = lookup(x)?
    result
}
"#;
    assert_eq!(jit_src_one_arg(src, 0), 404);
    assert_eq!(jit_src_one_arg(src, 7), 7);
}

/// `assert … else fail` clause: when the assertion fails at runtime the error
/// code is returned via `fail`, which `?` then propagates to the caller.
#[test]
fn bang_bang_assert_else_fail_propagates() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) {
    assert x > 0 else fail 400
    x
}

main : Int -> Nat !! HTTPError
main(x) {
    result : Int = fetch(x)?
    result
}
"#;
    // x <= 0: assert fails → fail 400 → decoded to 400 by `?`.
    assert_eq!(jit_src_one_arg(src, 0), 400);
    assert_eq!(jit_src_one_arg(src, -3), 400);
    // x > 0: assert holds → returns x.
    assert_eq!(jit_src_one_arg(src, 7), 7);
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
