use super::helpers::*;

// ── While loops ───────────────────────────────────────────────────────────────

#[test]
fn while_counts_to_n() {
    // main(n) counts from 0 up to n using a while loop and returns i (== n).
    let src = r#"
main : Nat -> Nat
main(n) {
    mut i: Nat = 0
    while i < n {
        i := i + 1
    }
    i
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 0);
    assert_eq!(jit_src_one_arg(src, 1), 1);
    assert_eq!(jit_src_one_arg(src, 5), 5);
    assert_eq!(jit_src_one_arg(src, 10), 10);
}

#[test]
fn while_sum_to_n() {
    // sum_to(n) = 1 + 2 + … + n  (== n*(n+1)/2)
    let src = r#"
main : Nat -> Nat
main(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc := acc + i
        i := i + 1
    }
    acc
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 0);
    assert_eq!(jit_src_one_arg(src, 1), 1);
    assert_eq!(jit_src_one_arg(src, 5), 15);
    assert_eq!(jit_src_one_arg(src, 10), 55);
}

#[test]
fn while_zero_iterations() {
    // Loop condition is false from the start — body never executes.
    let src = r#"
main : -> Int
main() {
    mut x: Int = 42
    while x < 0 {
        x := x - 1
    }
    x
}"#;
    assert_eq!(jit_src_zero_arg(src), 42);
}

#[test]
fn while_multiply_by_addition() {
    // a * b computed as repeated addition.
    let src = r#"
main : Nat -> Nat
main(n) {
    mut result: Nat = 0
    mut i: Nat = 0
    while i < n {
        result := result + 7
        i := i + 1
    }
    result
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 0);
    assert_eq!(jit_src_one_arg(src, 1), 7);
    assert_eq!(jit_src_one_arg(src, 6), 42);
}

// ── For-in loops ──────────────────────────────────────────────────────────────

#[test]
fn for_in_sum_set_literal() {
    // 1 + 2 + 3 = 6
    let src = r#"
main : -> Int
main() {
    mut acc: Int = 0
    for x in {1, 2, 3} {
        acc := acc + x
    }
    acc
}"#;
    assert_eq!(jit_src_zero_arg(src), 6);
}

#[test]
fn for_in_empty_set() {
    // Body never executes — acc stays at initial value.
    let src = r#"
main : -> Int
main() {
    mut acc: Int = 42
    for x in {} {
        acc := acc + 1
    }
    acc
}"#;
    assert_eq!(jit_src_zero_arg(src), 42);
}

#[test]
fn for_in_single_element() {
    // Exactly one iteration.
    let src = r#"
main : -> Int
main() {
    mut acc: Int = 0
    for x in {7} {
        acc := acc + x
    }
    acc
}"#;
    assert_eq!(jit_src_zero_arg(src), 7);
}

#[test]
fn for_in_uses_loop_var() {
    // The loop variable x is accessible inside the body.
    // Iterations: x=10, x=20, x=30 → last x wins as return.
    let src = r#"
main : -> Int
main() {
    mut last: Int = 0
    for x in {10, 20, 30} {
        last := x
    }
    last
}"#;
    assert_eq!(jit_src_zero_arg(src), 30);
}

#[test]
fn for_in_with_outer_param() {
    // The set elements are expressions that can reference function parameters.
    let src = r#"
main : Int -> Int
main(n) {
    mut acc: Int = 0
    for x in {1, 2, 3} {
        acc := acc + x + n
    }
    acc
}"#;
    // n=0: 1+2+3 = 6; n=10: (1+10)+(2+10)+(3+10) = 36
    assert_eq!(jit_src_one_arg(src, 0), 6);
    assert_eq!(jit_src_one_arg(src, 10), 36);
}

// ── For-in over comprehensions ────────────────────────────────────────────────

#[test]
fn for_in_comprehension_mapped_sum() {
    // Sum {x * 2 for x in {1, 3, 5}} = 2 + 6 + 10 = 18.
    let src = r#"
main : -> Int
main() {
    mut acc: Int = 0
    for y in {x * 2 for x in {1, 3, 5}} {
        acc := acc + y
    }
    acc
}"#;
    assert_eq!(jit_src_zero_arg(src), 18);
}

#[test]
fn for_in_comprehension_with_filter() {
    // {x for x in {1, 2, 3, 4, 5} if x > 2} = {3, 4, 5} → sum = 12.
    let src = r#"
main : -> Int
main() {
    mut acc: Int = 0
    for y in {x for x in {1, 2, 3, 4, 5} if x > 2} {
        acc := acc + y
    }
    acc
}"#;
    assert_eq!(jit_src_zero_arg(src), 12);
}

#[test]
fn for_in_comprehension_filter_all_out() {
    // Filter eliminates all elements — body never runs.
    let src = r#"
main : -> Int
main() {
    mut acc: Int = 99
    for y in {x for x in {1, 2, 3} if x > 10} {
        acc := acc + y
    }
    acc
}"#;
    assert_eq!(jit_src_zero_arg(src), 99);
}

#[test]
fn for_in_comprehension_captures_outer_param() {
    // Captured runtime variable `n` in both output and filter.
    // {x + n for x in {1, 2, 3} if x > 1} with n=10 → {12, 13} → sum = 25.
    let src = r#"
main : Int -> Int
main(n) {
    mut acc: Int = 0
    for y in {x + n for x in {1, 2, 3} if x > 1} {
        acc := acc + y
    }
    acc
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 5); // (2+0) + (3+0) = 5
    assert_eq!(jit_src_one_arg(src, 10), 25); // (2+10) + (3+10) = 25
}
