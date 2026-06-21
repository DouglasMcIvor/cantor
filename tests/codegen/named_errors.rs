use super::helpers::jit_src_one_arg;

// ── Named error set `?` propagation ──────────────────────────────────────────

/// On success `fetch` returns the input; `caller` should return it unchanged.
#[test]
fn named_error_try_success_path() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 400

caller : Int -> Int
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

/// On failure (input <= 0) `fetch` returns 400; `?` propagates it immediately.
#[test]
fn named_error_try_error_propagated() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 400

caller : Int -> Int
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

/// Verify that 503 is propagated when the callee returns it.
#[test]
fn named_error_503_propagated() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 503

main : Int -> Int
main(x) {
    result : Int = fetch(x)?
    result
}
"#;
    assert_eq!(jit_src_one_arg(src, 0), 503);
    assert_eq!(jit_src_one_arg(src, 10), 10);
}

/// Two sequential `?` calls: if the first fails the error short-circuits.
#[test]
fn named_error_chained_try_first_fails() {
    let src = r#"
HTTPError = {400, 503}

fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 400

main : Int -> Int
main(x) {
    a : Int = fetch(x)?
    b : Int = fetch(x + 1)?
    a + b
}
"#;
    // x = 0: first fetch(0) = 400, propagated immediately, b is never called.
    assert_eq!(jit_src_one_arg(src, 0), 400);
    // x = 5: fetch(5) = 5, fetch(6) = 6, result = 11.
    assert_eq!(jit_src_one_arg(src, 5), 11);
}

/// Named error set with a single element.
#[test]
fn named_error_single_element_set() {
    let src = r#"
NotFound = {404}

lookup : Int -> Nat | NotFound
lookup(x) = if x > 0 then x else 404

main : Int -> Int
main(x) {
    result : Int = lookup(x)?
    result
}
"#;
    assert_eq!(jit_src_one_arg(src, 0), 404);
    assert_eq!(jit_src_one_arg(src, 7), 7);
}

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
