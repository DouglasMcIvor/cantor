use super::helpers::{ir_for_src, jit_src_one_arg};

// ── Set(Int) literals ─────────────────────────────────────────────────────────

#[test]
fn set_literal_size() {
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Int) = {1, 2, 3}
             size(s)
         }",
        0,
    );
    assert_eq!(result, 3);
}

#[test]
fn set_literal_deduplicates() {
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Int) = {1, 2, 1, 3, 2}
             size(s)
         }",
        0,
    );
    assert_eq!(result, 3);
}

#[test]
fn set_literal_single_element() {
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Int) = {42}
             size(s)
         }",
        0,
    );
    assert_eq!(result, 1);
}

#[test]
fn set_literal_with_runtime_elements() {
    // Elements computed from the function parameter — forces runtime allocation.
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Int) = {n, n + 1, n + 2}
             size(s)
         }",
        10,
    );
    assert_eq!(result, 3);
}

#[test]
fn set_literal_runtime_elements_dedup() {
    // {n, n, n} deduplicates to a single-element set.
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Int) = {n, n, n}
             size(s)
         }",
        7,
    );
    assert_eq!(result, 1);
}

// ── IR inspection: compile-time vs runtime ────────────────────────────────────

/// `for x in {literal}` is compile-time unrolled — the IR must not contain any
/// calls to the runtime set allocator, since no heap set is ever created.
#[test]
fn for_in_literal_is_compile_time() {
    let ir = ir_for_src(
        "main : Int -> Int
         main(n) {
             mut acc : Int = 0
             for x in {1, 2, 3} {
                 acc := acc + x
             }
             acc
         }",
    );
    // Declarations (`declare i64 @cantor_set_new_i64()`) are always emitted by
    // declare_runtime_functions. We specifically check there are no call sites.
    assert!(
        !ir.lines().any(|l| l.contains("call") && l.contains("cantor_set_new")),
        "expected compile-time unrolling but found a runtime set allocation call:\n{ir}"
    );
}

/// `mut s : Set(Int) = {…}` IS a runtime set — the IR must contain a call to the allocator.
#[test]
fn mut_set_variable_is_runtime() {
    let ir = ir_for_src(
        "main : Int -> Int
         main(n) {
             mut s : Set(Int) = {1, 2, 3}
             size(s)
         }",
    );
    assert!(
        ir.lines().any(|l| l.contains("call") && l.contains("cantor_set_new_i64")),
        "expected a runtime set allocation call but none found:\n{ir}"
    );
}

// ── Set(Bool) literals ────────────────────────────────────────────────────────

#[test]
fn bool_set_literal_size() {
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Bool) = {true, false}
             size(s)
         }",
        0,
    );
    assert_eq!(result, 2);
}

#[test]
fn bool_set_literal_deduplicates() {
    let result = jit_src_one_arg(
        "main : Int -> Int
         main(n) {
             mut s : Set(Bool) = {true, true, false}
             size(s)
         }",
        0,
    );
    assert_eq!(result, 2);
}
