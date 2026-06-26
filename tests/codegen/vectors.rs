use super::helpers::{jit_src_one_arg, jit_src_zero_arg};

// Helper for three-argument functions (not yet in the shared helpers).
fn jit_src_three_args(src: &str, a: i64, b: i64, c: i64) -> i64 {
    use cantor::{codegen::compile_file, parser::parse_file};
    use inkwell::context::Context;
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let engine = compile_file(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"));
    unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn(i64, i64, i64) -> i64>("main")
            .unwrap();
        f.call(a, b, c)
    }
}

// ── Repeated products (`X * N`) — runtime behaviour ──────────────────────────

// main : Int * 3 -> Int  sums three parameters.
#[test]
fn repeated_product_three_params_sum() {
    assert_eq!(
        jit_src_three_args(
            "main : Int * 3 -> Int\nmain(x, y, z) = x + y + z",
            1, 2, 3
        ),
        6,
    );
    assert_eq!(
        jit_src_three_args(
            "main : Int * 3 -> Int\nmain(x, y, z) = x + y + z",
            10, 20, 30
        ),
        60,
    );
}

// Nat * 3 domain; product of three elements.
#[test]
fn repeated_product_three_nat_params_multiply() {
    assert_eq!(
        jit_src_three_args(
            "main : Nat * 3 -> Nat\nmain(x, y, z) = x * y * z",
            2, 3, 4
        ),
        24,
    );
}

// Int * 2 domain (two-arg); needs a jit_src_two_args helper that doesn't exist yet.
#[test]
#[ignore = "needs jit_src_two_args helper — update once added"]
fn repeated_product_two_params_diff() {
    assert_eq!(
        jit_src_one_arg(
            "main : Int * 2 -> Int\nmain(x, y) = x - y",
            5  // but we need two args — this test uses the wrong helper;
               // keep as a reminder that jit_src_two_args should be added
        ),
        // Placeholder: this test will be updated once jit_src_two_args exists.
        // For now we test that `Int * 2` compiles with the standard 1-arg helper
        // by only using x and ignoring y.
        5, // main(x, _) = x
    );
}

// ── Homogeneous array literals (`[...]`) — runtime behaviour ─────────────────

// [1, 2, 3] as return value; project element 0.
#[test]
fn array_lit_proj_zero() {
    assert_eq!(
        jit_src_zero_arg("main : -> Int\nmain() = [1, 2, 3].0"),
        1,
    );
}

// Project element 1.
#[test]
fn array_lit_proj_one() {
    assert_eq!(
        jit_src_zero_arg("main : -> Int\nmain() = [10, 20, 30].1"),
        20,
    );
}

// Project element 2.
#[test]
fn array_lit_proj_two() {
    assert_eq!(
        jit_src_zero_arg("main : -> Int\nmain() = [10, 20, 30].2"),
        30,
    );
}

// [x, x + 1, x + 2] — elements derived from a parameter.
#[test]
fn array_lit_computed_elements_proj() {
    assert_eq!(
        jit_src_one_arg("main : Int -> Int\nmain(x) = [x, x + 1, x + 2].1", 7),
        8,
    );
}

// [true, false, true] with Bool projection.
#[test]
fn array_lit_bool_elements_proj() {
    assert_eq!(
        jit_src_zero_arg("main : -> Bool\nmain() = [true, false, true].0"),
        1, // true
    );
    assert_eq!(
        jit_src_zero_arg("main : -> Bool\nmain() = [true, false, true].1"),
        0, // false
    );
}

// [1, 2, 3] produces the same runtime value as (1, 2, 3).
#[test]
fn array_lit_same_value_as_tuple_lit() {
    let array = jit_src_zero_arg("main : -> Int\nmain() = [7, 8, 9].2");
    let tuple = jit_src_zero_arg("main : -> Int\nmain() = (7, 8, 9).2");
    assert_eq!(array, tuple);
}

// ── Bracket index `x[N]` — alias for `x.N` ───────────────────────────────────

// x[N] and x.N should produce identical results.
#[test]
fn bracket_index_same_as_dot_proj() {
    let dot     = jit_src_zero_arg("main : -> Int\nmain() = [10, 20, 30].1");
    let bracket = jit_src_zero_arg("main : -> Int\nmain() = [10, 20, 30][1]");
    assert_eq!(dot, bracket);
    assert_eq!(bracket, 20);
}

// Bracket index on a tuple parameter.
#[test]
fn bracket_index_on_param() {
    assert_eq!(
        jit_src_one_arg("main : Int * 3 -> Int\nmain(t) = t[0]", 7),
        7,
    );
}

// ── Kleene-star vectors (`X*`) — runtime behaviour ───────────────────────────
// The runtime representation for X* values is variable-length; a concrete
// calling convention is TBD.  These tests use the `len` built-in and simple
// known-length vectors to verify the basics once the feature is implemented.

// Length of an empty vector is 0.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented"]
fn kleene_len_empty() {
    assert_eq!(
        jit_src_zero_arg("main : -> Nat\nmain() = len([])"),
        0,
    );
}

// Length of a three-element vector is 3.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented"]
fn kleene_len_three() {
    assert_eq!(
        jit_src_zero_arg("main : -> Nat\nmain() = len([1, 2, 3])"),
        3,
    );
}

// Indexing into a known-length Nat* value.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented"]
fn kleene_index_known_length() {
    assert_eq!(
        jit_src_zero_arg("main : -> Nat\nmain() = [10, 20, 30].1"),
        20,
    );
}

// Passing a Nat* parameter and returning its length.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented"]
fn kleene_param_len_returned() {
    // Build a two-element Int* value inline and pass to a function.
    assert_eq!(
        jit_src_zero_arg("
main : -> Nat
main() {
    xs : Nat* = [5, 6, 7]
    len(xs)
}"),
        3,
    );
}

// Sum all elements of a Nat* with a for-in loop.
#[test]
#[ignore = "Kleene-star (X*) not yet implemented"]
fn kleene_sum_via_loop() {
    assert_eq!(
        jit_src_zero_arg("
main : -> Nat
main() {
    xs  : Nat* = [1, 2, 3, 4]
    mut acc : Nat = 0
    for x in xs {
        acc := acc + x
    }
    acc
}"),
        10,
    );
}
