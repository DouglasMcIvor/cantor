use super::helpers::*;
use cantor::ast::{BinOp, Param, UnOp};
use cantor::codegen::Compiler;
use cantor::kind::Kind;
use cantor::semantics::tree::SemExpr;
use inkwell::context::Context;

// ── Literals ──────────────────────────────────────────────────────────────────

#[test]
fn int_literal() {
    assert_eq!(jit_eval(SemExpr::int(42)), 42);
}

#[test]
fn int_literal_negative() {
    assert_eq!(jit_eval(SemExpr::int(-7)), -7);
}

#[test]
fn bool_true() {
    assert_eq!(jit_eval(SemExpr::bool(true)), 1);
}

#[test]
fn bool_false() {
    assert_eq!(jit_eval(SemExpr::bool(false)), 0);
}

// ── Arithmetic ────────────────────────────────────────────────────────────────

#[test]
fn add() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Add, SemExpr::int(1), SemExpr::int(2))), 3);
}

#[test]
fn sub() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Sub, SemExpr::int(5), SemExpr::int(3))), 2);
}

#[test]
fn mul() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Mul, SemExpr::int(3), SemExpr::int(4))), 12);
}

#[test]
fn div_truncates() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Div, SemExpr::int(10), SemExpr::int(3))), 3);
}

#[test]
fn neg() {
    assert_eq!(jit_eval(SemExpr::unop(UnOp::Neg, SemExpr::int(5))), -5);
}

#[test]
fn nested_arithmetic() {
    // (2 + 3) * (10 - 4)  =  5 * 6  =  30
    let expr = SemExpr::binop(
        BinOp::Mul,
        SemExpr::binop(BinOp::Add, SemExpr::int(2), SemExpr::int(3)),
        SemExpr::binop(BinOp::Sub, SemExpr::int(10), SemExpr::int(4)),
    );
    assert_eq!(jit_eval(expr), 30);
}

// ── Comparisons (return 0 or 1) ───────────────────────────────────────────────

#[test]
fn eq_true() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Eq, SemExpr::int(3), SemExpr::int(3))), 1);
}

#[test]
fn eq_false() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Eq, SemExpr::int(3), SemExpr::int(4))), 0);
}

#[test]
fn ne() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Ne, SemExpr::int(1), SemExpr::int(2))), 1);
}

#[test]
fn lt_true() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Lt, SemExpr::int(3), SemExpr::int(4))), 1);
}

#[test]
fn lt_false() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Lt, SemExpr::int(4), SemExpr::int(3))), 0);
}

#[test]
fn le_equal() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Le, SemExpr::int(3), SemExpr::int(3))), 1);
}

#[test]
fn gt() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Gt, SemExpr::int(5), SemExpr::int(2))), 1);
}

#[test]
fn ge_equal() {
    assert_eq!(jit_eval(SemExpr::binop(BinOp::Ge, SemExpr::int(3), SemExpr::int(3))), 1);
}

// ── Logic ─────────────────────────────────────────────────────────────────────

#[test]
fn and_both_true() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::And, SemExpr::bool(true), SemExpr::bool(true))),
        1
    );
}

#[test]
fn and_one_false() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::And, SemExpr::bool(true), SemExpr::bool(false))),
        0
    );
}

#[test]
fn or_one_true() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Or, SemExpr::bool(false), SemExpr::bool(true))),
        1
    );
}

#[test]
fn not_true() {
    assert_eq!(jit_eval(SemExpr::unop(UnOp::Not, SemExpr::bool(true))), 0);
}

#[test]
fn not_false() {
    assert_eq!(jit_eval(SemExpr::unop(UnOp::Not, SemExpr::bool(false))), 1);
}

// ── Variables & function parameters ──────────────────────────────────────────

#[test]
fn identity_function() {
    let result = jit_eval_fn(&[Param::new("x")], SemExpr::var("x", Kind::Int), &[99]);
    assert_eq!(result, 99);
}

#[test]
fn add_two_params() {
    let body = SemExpr::binop(BinOp::Add, SemExpr::var("x", Kind::Int), SemExpr::var("y", Kind::Int));
    assert_eq!(jit_eval_fn(&[Param::new("x"), Param::new("y")], body, &[10, 32]), 42);
}

#[test]
fn param_arithmetic() {
    // f(x) = x * x - 1
    let body = SemExpr::binop(
        BinOp::Sub,
        SemExpr::binop(BinOp::Mul, SemExpr::var("x", Kind::Int), SemExpr::var("x", Kind::Int)),
        SemExpr::int(1),
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
    compiler.declare_runtime_functions();

    let double_body = SemExpr::binop(BinOp::Mul, SemExpr::var("x", Kind::Int), SemExpr::int(2));
    compiler.compile_function("double", &[Param::new("x")], &double_body).unwrap();

    let main_body = SemExpr::call("double", vec![SemExpr::int(21)], Kind::Int);
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
