use super::helpers::*;

#[test]
fn let_binding_basic_value() {
    let src = r#"
main : -> Int
main() {
    x : Int = 42
    x
}"#;
    assert_eq!(jit_src_zero_arg(src), 42);
}

#[test]
fn let_binding_used_in_expression() {
    let src = r#"
main : Nat -> Nat
main(n) {
    offset : Nat = 10
    n + offset
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 10);
    assert_eq!(jit_src_one_arg(src, 5), 15);
}

#[test]
fn let_multiple_bindings_compose() {
    let src = r#"
main : Nat -> Nat
main(n) {
    a : Nat = n + 1
    b : Nat = a + a
    b
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 2);
    assert_eq!(jit_src_one_arg(src, 3), 8);
}

#[test]
fn let_and_mut_in_loop() {
    let src = r#"
main : Nat -> Nat
main(n) {
    step : Nat = 2
    mut acc : Nat = 0
    mut i : Nat = 0
    while i < n {
        acc := acc + step
        i := i + 1
    }
    acc
}"#;
    assert_eq!(jit_src_one_arg(src, 0), 0);
    assert_eq!(jit_src_one_arg(src, 1), 2);
    assert_eq!(jit_src_one_arg(src, 5), 10);
}
