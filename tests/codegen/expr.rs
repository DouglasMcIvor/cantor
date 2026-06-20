use super::helpers::*;
use cantor::ast::{BinOp, Expr, Param, UnOp};
use cantor::codegen::Compiler;
use inkwell::context::Context;

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

// ── Bool-returning functions via compile_file ─────────────────────────────────

#[test]
fn bool_returning_function_true() {
    // is_positive : Int -> Bool / is_positive(x) = x > 0
    // main called with 5 → 1
    assert_eq!(
        jit_src_one_arg(
            "is_positive : Int -> Bool\nis_positive(x) = x > 0\nmain : Int -> Bool\nmain(x) = is_positive(x)",
            5
        ),
        1
    );
}

#[test]
fn bool_returning_function_false() {
    assert_eq!(
        jit_src_one_arg(
            "is_positive : Int -> Bool\nis_positive(x) = x > 0\nmain : Int -> Bool\nmain(x) = is_positive(x)",
            -3
        ),
        0
    );
}

#[test]
fn bool_returning_function_negated() {
    // negate(b) = not is_positive(b)  — exercises call result truncation
    assert_eq!(
        jit_src_one_arg(
            "is_positive : Int -> Bool\n\
             is_positive(x) = x > 0\n\
             negate_pos : Int -> Bool\n\
             negate_pos(x) = not is_positive(x)\n\
             main : Int -> Bool\n\
             main(x) = negate_pos(x)",
            5
        ),
        0
    );
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
