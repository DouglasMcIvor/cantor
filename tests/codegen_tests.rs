use cantor::{
    ast::{BinOp, Expr, Param, UnOp},
    codegen::Compiler,
};
use inkwell::context::Context;

/// Compile `body` as a zero-parameter function and JIT-execute it.
/// All results come back as i64 (bools are zero-extended by compile_function).
fn jit_eval(body: Expr) -> i64 {
    jit_eval_fn(&[], body, &[])
}

/// Compile a function with the given params/body, call it with `args`.
fn jit_eval_fn(params: &[Param], body: Expr, args: &[i64]) -> i64 {
    let ctx = Context::create();
    let mut compiler = Compiler::new(&ctx, "test");
    compiler.compile_function("__test__", params, &body).unwrap();
    let engine = compiler.into_jit_engine().unwrap();
    unsafe {
        match args.len() {
            0 => {
                let f = engine
                    .get_function::<unsafe extern "C" fn() -> i64>("__test__")
                    .unwrap();
                f.call()
            }
            1 => {
                let f = engine
                    .get_function::<unsafe extern "C" fn(i64) -> i64>("__test__")
                    .unwrap();
                f.call(args[0])
            }
            2 => {
                let f = engine
                    .get_function::<unsafe extern "C" fn(i64, i64) -> i64>("__test__")
                    .unwrap();
                f.call(args[0], args[1])
            }
            _ => panic!("jit_eval_fn: add more arms for >{} params", args.len()),
        }
    }
}

// ── Literals ──────────────────────────────────────────────────────────────────

#[test]
fn int_literal() {
    assert_eq!(jit_eval(Expr::int(42)), 42);
}

#[test]
fn int_literal_negative() {
    assert_eq!(jit_eval(Expr::int(-7)), -7);
}

#[test]
fn bool_true() {
    assert_eq!(jit_eval(Expr::bool(true)), 1);
}

#[test]
fn bool_false() {
    assert_eq!(jit_eval(Expr::bool(false)), 0);
}

// ── Arithmetic ────────────────────────────────────────────────────────────────

#[test]
fn add() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Add, Expr::int(1), Expr::int(2))), 3);
}

#[test]
fn sub() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Sub, Expr::int(5), Expr::int(3))), 2);
}

#[test]
fn mul() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Mul, Expr::int(3), Expr::int(4))), 12);
}

#[test]
fn div_truncates() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Div, Expr::int(10), Expr::int(3))), 3);
}

#[test]
fn neg() {
    assert_eq!(jit_eval(Expr::unop(UnOp::Neg, Expr::int(5))), -5);
}

#[test]
fn nested_arithmetic() {
    // (2 + 3) * (10 - 4)  =  5 * 6  =  30
    let expr = Expr::binop(
        BinOp::Mul,
        Expr::binop(BinOp::Add, Expr::int(2), Expr::int(3)),
        Expr::binop(BinOp::Sub, Expr::int(10), Expr::int(4)),
    );
    assert_eq!(jit_eval(expr), 30);
}

// ── Comparisons (return 0 or 1) ───────────────────────────────────────────────

#[test]
fn eq_true() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Eq, Expr::int(3), Expr::int(3))), 1);
}

#[test]
fn eq_false() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Eq, Expr::int(3), Expr::int(4))), 0);
}

#[test]
fn ne() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Ne, Expr::int(1), Expr::int(2))), 1);
}

#[test]
fn lt_true() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Lt, Expr::int(3), Expr::int(4))), 1);
}

#[test]
fn lt_false() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Lt, Expr::int(4), Expr::int(3))), 0);
}

#[test]
fn le_equal() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Le, Expr::int(3), Expr::int(3))), 1);
}

#[test]
fn gt() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Gt, Expr::int(5), Expr::int(2))), 1);
}

#[test]
fn ge_equal() {
    assert_eq!(jit_eval(Expr::binop(BinOp::Ge, Expr::int(3), Expr::int(3))), 1);
}

// ── Logic ─────────────────────────────────────────────────────────────────────

#[test]
fn and_both_true() {
    assert_eq!(
        jit_eval(Expr::binop(BinOp::And, Expr::bool(true), Expr::bool(true))),
        1
    );
}

#[test]
fn and_one_false() {
    assert_eq!(
        jit_eval(Expr::binop(BinOp::And, Expr::bool(true), Expr::bool(false))),
        0
    );
}

#[test]
fn or_one_true() {
    assert_eq!(
        jit_eval(Expr::binop(BinOp::Or, Expr::bool(false), Expr::bool(true))),
        1
    );
}

#[test]
fn not_true() {
    assert_eq!(jit_eval(Expr::unop(UnOp::Not, Expr::bool(true))), 0);
}

#[test]
fn not_false() {
    assert_eq!(jit_eval(Expr::unop(UnOp::Not, Expr::bool(false))), 1);
}

// ── Variables & function parameters ──────────────────────────────────────────

#[test]
fn identity_function() {
    let result = jit_eval_fn(&[Param::new("x")], Expr::var("x"), &[99]);
    assert_eq!(result, 99);
}

#[test]
fn add_two_params() {
    let body = Expr::binop(BinOp::Add, Expr::var("x"), Expr::var("y"));
    assert_eq!(jit_eval_fn(&[Param::new("x"), Param::new("y")], body, &[10, 32]), 42);
}

#[test]
fn param_arithmetic() {
    // f(x) = x * x - 1
    let body = Expr::binop(
        BinOp::Sub,
        Expr::binop(BinOp::Mul, Expr::var("x"), Expr::var("x")),
        Expr::int(1),
    );
    assert_eq!(jit_eval_fn(&[Param::new("x")], body, &[5]), 24);
}

// ── Cross-function calls ──────────────────────────────────────────────────────

#[test]
fn call_other_function() {
    // double(x) = x * 2
    // main()    = double(21)
    let ctx = Context::create();
    let mut compiler = Compiler::new(&ctx, "test_call");

    let double_body = Expr::binop(BinOp::Mul, Expr::var("x"), Expr::int(2));
    compiler.compile_function("double", &[Param::new("x")], &double_body).unwrap();

    let main_body = Expr::call("double", vec![Expr::int(21)]);
    compiler.compile_function("main", &[], &main_body).unwrap();

    let engine = compiler.into_jit_engine().unwrap();
    let result = unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn() -> i64>("main")
            .unwrap();
        f.call()
    };
    assert_eq!(result, 42);
}

// ── While loops ──────────────────────────────────────────────────────────────

/// Parse `src` as a Cantor source file, compile it, and call `main(arg)`.
fn jit_src_one_arg(src: &str, arg: i64) -> i64 {
    use cantor::{parser::parse_file, codegen::compile_file};
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let engine = compile_file(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"));
    unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn(i64) -> i64>("main")
            .unwrap();
        f.call(arg)
    }
}

/// Parse `src`, compile, and call zero-arg `main()`.
fn jit_src_zero_arg(src: &str) -> i64 {
    use cantor::{parser::parse_file, codegen::compile_file};
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let engine = compile_file(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"));
    unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn() -> i64>("main")
            .unwrap();
        f.call()
    }
}

#[test]
fn while_counts_to_n() {
    // main(n) counts from 0 up to n using a while loop and returns i (== n).
    let src = r#"
main : Nat -> Nat
main(n) {
    mut i: Nat = 0
    while i < n {
        i = i + 1
    }
    i
}"#;
    assert_eq!(jit_src_one_arg(src, 0),  0);
    assert_eq!(jit_src_one_arg(src, 1),  1);
    assert_eq!(jit_src_one_arg(src, 5),  5);
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
        acc = acc + i
        i = i + 1
    }
    acc
}"#;
    assert_eq!(jit_src_one_arg(src, 0),  0);
    assert_eq!(jit_src_one_arg(src, 1),  1);
    assert_eq!(jit_src_one_arg(src, 5),  15);
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
        x = x - 1
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
        result = result + 7
        i = i + 1
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
        acc = acc + x
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
        acc = acc + 1
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
        acc = acc + x
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
        last = x
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
        acc = acc + x + n
    }
    acc
}"#;
    // n=0: 1+2+3 = 6; n=10: (1+10)+(2+10)+(3+10) = 36
    assert_eq!(jit_src_one_arg(src, 0),  6);
    assert_eq!(jit_src_one_arg(src, 10), 36);
}
