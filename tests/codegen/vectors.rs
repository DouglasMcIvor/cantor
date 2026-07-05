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
        jit_src_three_args("main : Int * 3 -> Int\nmain(x, y, z) = x + y + z", 1, 2, 3),
        6,
    );
    assert_eq!(
        jit_src_three_args(
            "main : Int * 3 -> Int\nmain(x, y, z) = x + y + z",
            10,
            20,
            30
        ),
        60,
    );
}

// Nat * 3 domain; product of three elements.
#[test]
fn repeated_product_three_nat_params_multiply() {
    assert_eq!(
        jit_src_three_args("main : Nat * 3 -> Nat\nmain(x, y, z) = x * y * z", 2, 3, 4),
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
            5 // but we need two args — this test uses the wrong helper;
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
    assert_eq!(jit_src_zero_arg("main : -> Int\nmain() = [1, 2, 3].0"), 1,);
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
    let dot = jit_src_zero_arg("main : -> Int\nmain() = [10, 20, 30].1");
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
fn kleene_len_empty() {
    assert_eq!(jit_src_zero_arg("main : -> Nat\nmain() = len([])"), 0,);
}

// Length of a three-element vector is 3.
#[test]
fn kleene_len_three() {
    assert_eq!(
        jit_src_zero_arg("main : -> Nat\nmain() = len([1, 2, 3])"),
        3,
    );
}

// Indexing into a known-length Nat* value.
#[test]
fn kleene_index_known_length() {
    assert_eq!(
        jit_src_zero_arg("main : -> Nat\nmain() = [10, 20, 30].1"),
        20,
    );
}

// Passing a Nat* parameter and returning its length.
#[test]
fn kleene_param_len_returned() {
    // Build a two-element Int* value inline and pass to a function.
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    xs : Nat* = [5, 6, 7]
    len(xs)
}"
        ),
        3,
    );
}

// ── Union vectors ─────────────────────────────────────────────────────────────
//
// `(Nat | (Nat * Bool))*` — a TaggedUnion element kind.
// Arm 0 = Nat (1 leaf); arm 1 = Nat * Bool (2 leaves).

#[test]
fn union_vec_len() {
    // Two arm-0 elements and one arm-1 element → length 3.
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    xs : (Nat | (Nat * Bool))* = [1, (2, true), 3]
    len(xs)
}"
        ),
        3,
    );
}

#[test]
fn union_vec_scalar_arm_index() {
    // xs[0] is a Nat arm; access its single leaf via arm tag.
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    xs : (Nat | (Nat * Bool))* = [42, (1, false)]
    xs[0].1
}"
        ),
        42,
    );
}

#[test]
fn union_vec_tuple_arm_index() {
    // xs[1] is a (Nat * Bool) arm; extract the Bool field.
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    xs : (Nat | (Nat * Bool))* = [99, (7, true)]
    xs[1].2
}"
        ),
        1, // true as i64
    );
}

#[test]
fn union_vec_concat_len() {
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    a : (Nat | (Nat * Bool))* = [1, (2, true)]
    b : (Nat | (Nat * Bool))* = [(3, false), 4]
    len(a ++ b)
}"
        ),
        4,
    );
}

// ── Runtime (dynamic) index `xs[i]` where `i` is not a literal ───────────────
//
// A literal index (`xs[0]`) parses to `Proj` and never reaches
// `compile_index`. These tests use a parameter as the index so the parser
// produces an `Index` node and exercises `compile_index`'s runtime-call path
// instead.

// Dynamic index into a scalar (`Nat*`) vector.
#[test]
fn dynamic_index_scalar_vec() {
    assert_eq!(
        jit_src_one_arg(
            "
main : Nat -> Nat
main(i) {
    xs : Nat* = [10, 20, 30]
    xs[i]
}",
            1,
        ),
        20,
    );
}

// Dynamic index into a `Nat**` (vector-of-vector) value, then `len` the row.
#[test]
fn dynamic_index_nested_vec() {
    assert_eq!(
        jit_src_one_arg(
            "
main : Nat -> Nat
main(i) {
    xs : Nat** = [[1, 2], [3, 4, 5]]
    len(xs[i])
}",
            1,
        ),
        3,
    );
}

// Dynamic index into a union vector — exercises `compile_index`'s
// `Kind::TaggedUnion` arm (`compile_union_vec_index`), previously only
// reached via a literal `Proj` index in the tests above.
#[test]
fn dynamic_index_union_vec() {
    assert_eq!(
        jit_src_one_arg(
            "
main : Nat -> Nat
main(i) {
    xs : (Nat | (Nat * Bool))* = [42, (1, false)]
    xs[i].1
}",
            0,
        ),
        42,
    );
}

// ── Tuple-element vectors (`(A * B)*`), no union wrapper ─────────────────────
//
// Every other vector-of-tuples test in this file wraps the tuple in a
// `(Nat | (Nat * Bool))*` union, which exercises `compile_union_vec_index`
// rather than the plain-tuple struct-vector path. These tests build a
// `(Nat * Bool)*` value directly, exercising `compile_tuple_as_struct_vec`
// (construction) and `compile_struct_vec_index` (element access) with no
// union involved.

// Literal index into a struct vector, then project a field: `xs[1].0`.
#[test]
fn struct_vec_literal_index() {
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    xs : (Nat * Bool)* = [(1, true), (2, false)]
    xs[1].0
}"
        ),
        2,
    );
}

// Same, but with a Bool field to check the i64/bool packing round-trips.
#[test]
fn struct_vec_literal_index_bool_field() {
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Bool
main() {
    xs : (Nat * Bool)* = [(1, true), (2, false)]
    xs[0].1
}"
        ),
        1, // true as i64
    );
}

// Dynamic index into a struct vector — exercises `compile_index`'s
// `Kind::Tuple` arm, which forwards straight into `compile_struct_vec_index`.
#[test]
fn struct_vec_dynamic_index() {
    assert_eq!(
        jit_src_one_arg(
            "
main : Nat -> Nat
main(i) {
    xs : (Nat * Bool)* = [(1, true), (2, false)]
    xs[i].0
}",
            1,
        ),
        2,
    );
}

// `len` and `++` on a struct vector.
#[test]
fn struct_vec_len_and_concat() {
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    a : (Nat * Bool)* = [(1, true)]
    b : (Nat * Bool)* = [(2, false), (3, true)]
    len(a ++ b)
}"
        ),
        3,
    );
}

// Sum all elements of a Nat* with a for-in loop.
#[test]
#[ignore = "for over sequences not yet implemented"]
fn kleene_sum_via_loop() {
    assert_eq!(
        jit_src_zero_arg(
            "
main : -> Nat
main() {
    xs  : Nat* = [1, 2, 3, 4]
    mut acc : Nat = 0
    for x in xs {
        acc := acc + x
    }
    acc
}"
        ),
        10,
    );
}
