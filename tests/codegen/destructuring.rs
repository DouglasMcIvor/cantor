use super::helpers::*;

// ── DestructLet: immutable destructuring ─────────────────────────────────────

#[test]
fn destruct_let_sum_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    x, y = (-3, 4)
    x + y
}
",
    );
    assert_eq!(result, 1);
}

#[test]
fn destruct_let_with_constraints_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    x : Int, y : Int = (10, 7)
    x - y
}
",
    );
    assert_eq!(result, 3);
}

#[test]
fn destruct_let_three_elements_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    a, b, c = (1, 2, 3)
    a + b + c
}
",
    );
    assert_eq!(result, 6);
}

#[test]
fn destruct_let_from_param_runs() {
    let result = jit_src_one_arg(
        "
main : Int -> Int
main(n) {
    x, y = (n, n + 1)
    x + y
}
",
        5,
    );
    assert_eq!(result, 11);
}

// ── DestructMutLet: mutable destructuring ────────────────────────────────────

#[test]
fn destruct_mut_let_then_reassign_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    mut a : Int, b : Int = (-3, 4)
    a := b
    a
}
",
    );
    assert_eq!(result, 4);
}

// ── Partial destructuring: last binder collects tail ─────────────────────────

#[test]
fn partial_destruct_two_binders_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    a, rest = (1, 2, 3)
    a + rest.0 + rest.1
}
",
    );
    assert_eq!(result, 6);
}

#[test]
fn partial_destruct_three_binders_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    a, b, rest = (1, 2, 3, 4)
    a + b + rest.0 + rest.1
}
",
    );
    assert_eq!(result, 10);
}

#[test]
fn partial_destruct_from_param_runs() {
    let result = jit_src_one_arg(
        "
main : Int -> Int
main(n) {
    a, rest = (n, n + 1, n + 2)
    a + rest.0 + rest.1
}
",
        10,
    );
    // 10 + 11 + 12 = 33
    assert_eq!(result, 33);
}

// ── DestructAssign: reassignment of existing mutables ────────────────────────

#[test]
fn destruct_assign_swap_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    mut a : Int, b : Int = (-3, 4)
    a, b := (b, a)
    a
}
",
    );
    // a should become 4 after swap
    assert_eq!(result, 4);
}

#[test]
fn destruct_assign_sum_after_swap_runs() {
    let result = jit_src_zero_arg(
        "
main : -> Int
main() {
    mut a : Int, b : Int = (10, 20)
    a, b := (b, a)
    a + b
}
",
    );
    // sum is preserved across swap
    assert_eq!(result, 30);
}
