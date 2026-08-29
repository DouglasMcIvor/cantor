use super::helpers::*;
use cantor::ast::{BinOp, Param, UnOp};
use cantor::codegen::Compiler;
use cantor::kind::Kind;
use cantor::semantics::tree::{SemExpr, SemExprKind};
use cantor::span::Span;
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
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Add, SemExpr::int(1), SemExpr::int(2))),
        3
    );
}

#[test]
fn sub() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Sub, SemExpr::int(5), SemExpr::int(3))),
        2
    );
}

#[test]
fn mul() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Mul, SemExpr::int(3), SemExpr::int(4))),
        12
    );
}

#[test]
fn quot_truncates() {
    // `quot` is the integer-division operator. `/` is exact and yields a
    // Rational, so it has no meaningful reading in this harness — `jit_eval`
    // returns an i64, and a Rational is a pointer. (A `/` here would instead
    // exercise the narrowing guard: `compile_function`'s test wrapper always
    // declares a `Kind::Int` return, so `10 / 3` aborts in
    // `cantor_rational_to_int` rather than silently truncating — which is the
    // intended behaviour, just not a useful assertion.)
    assert_eq!(
        jit_eval(SemExpr::new(
            SemExprKind::BinOp {
                op: BinOp::Quot,
                lhs: Box::new(SemExpr::int(10)),
                rhs: Box::new(SemExpr::int(3)),
            },
            Kind::Int,
            Span::dummy(),
        )),
        3
    );
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
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Eq, SemExpr::int(3), SemExpr::int(3))),
        1
    );
}

#[test]
fn eq_false() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Eq, SemExpr::int(3), SemExpr::int(4))),
        0
    );
}

#[test]
fn ne() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Ne, SemExpr::int(1), SemExpr::int(2))),
        1
    );
}

#[test]
fn lt_true() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Lt, SemExpr::int(3), SemExpr::int(4))),
        1
    );
}

#[test]
fn lt_false() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Lt, SemExpr::int(4), SemExpr::int(3))),
        0
    );
}

#[test]
fn le_equal() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Le, SemExpr::int(3), SemExpr::int(3))),
        1
    );
}

#[test]
fn gt() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Gt, SemExpr::int(5), SemExpr::int(2))),
        1
    );
}

#[test]
fn ge_equal() {
    assert_eq!(
        jit_eval(SemExpr::binop(BinOp::Ge, SemExpr::int(3), SemExpr::int(3))),
        1
    );
}

// ── Logic ─────────────────────────────────────────────────────────────────────

#[test]
fn and_both_true() {
    assert_eq!(
        jit_eval(SemExpr::binop(
            BinOp::And,
            SemExpr::bool(true),
            SemExpr::bool(true)
        )),
        1
    );
}

#[test]
fn and_one_false() {
    assert_eq!(
        jit_eval(SemExpr::binop(
            BinOp::And,
            SemExpr::bool(true),
            SemExpr::bool(false)
        )),
        0
    );
}

#[test]
fn or_one_true() {
    assert_eq!(
        jit_eval(SemExpr::binop(
            BinOp::Or,
            SemExpr::bool(false),
            SemExpr::bool(true)
        )),
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
    let body = SemExpr::binop(
        BinOp::Add,
        SemExpr::var("x", Kind::Int),
        SemExpr::var("y", Kind::Int),
    );
    assert_eq!(
        jit_eval_fn(&[Param::new("x"), Param::new("y")], body, &[10, 32]),
        42
    );
}

#[test]
fn param_arithmetic() {
    // f(x) = x * x - 1
    let body = SemExpr::binop(
        BinOp::Sub,
        SemExpr::binop(
            BinOp::Mul,
            SemExpr::var("x", Kind::Int),
            SemExpr::var("x", Kind::Int),
        ),
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

// ── Float32 ───────────────────────────────────────────────────────────────────
//
// `jit_eval` always returns the ABI-widened i64 word (bitcast f32 -> i32,
// zero-extended — see `codegen::Compiler::widen_scalar_to_i64`), so every
// assertion here decodes it back via `f32::from_bits(result as u32)`.

fn jit_eval_f32(body: SemExpr) -> f32 {
    f32::from_bits(jit_eval(body) as u32)
}

#[test]
fn float32_literal() {
    assert_eq!(jit_eval_f32(SemExpr::float32(2.5)), 2.5);
}

#[test]
fn float32_literal_nan_bit_exact() {
    // Built via the raw IEEE bit pattern at codegen time — must round-trip
    // exactly, not just "some NaN" (see `compile_expr`'s `FloatLit` arm).
    assert_eq!(
        jit_eval(SemExpr::float32(f32::NAN)) as u32,
        f32::NAN.to_bits()
    );
}

#[test]
fn float32_add() {
    let body = SemExpr::new(
        SemExprKind::Add(
            Box::new(SemExpr::float32(1.5)),
            Box::new(SemExpr::float32(2.25)),
        ),
        Kind::Float32,
        Span::dummy(),
    );
    assert_eq!(jit_eval_f32(body), 3.75);
}

#[test]
fn float32_div_by_zero_is_infinity_not_a_trap() {
    // Float32 division is total under IEEE 754 — no runtime guard, unlike Int.
    let body = SemExpr::new(
        SemExprKind::Div(
            Box::new(SemExpr::float32(1.0)),
            Box::new(SemExpr::float32(0.0)),
        ),
        Kind::Float32,
        Span::dummy(),
    );
    assert_eq!(jit_eval_f32(body), f32::INFINITY);
}

#[test]
fn float32_neg_is_a_sign_bit_flip_for_negative_zero() {
    // `-0.0f - x` would give `+0.0f` under real IEEE subtraction — this
    // must be a genuine `fneg`, not `0.0f - x` (docs/design-decisions.md's
    // `Float32` section).
    let body = SemExpr::unop(UnOp::Neg, SemExpr::float32(0.0));
    let body = SemExpr::new(body.kind, Kind::Float32, Span::dummy());
    let result = jit_eval(body) as u32;
    assert_eq!(result, (-0.0f32).to_bits());
    assert_ne!(result, 0.0f32.to_bits());
}

#[test]
fn float32_ordered_comparison_false_for_nan() {
    let body = SemExpr::new(
        SemExprKind::BinOp {
            op: BinOp::Lt,
            lhs: Box::new(SemExpr::float32(f32::NAN)),
            rhs: Box::new(SemExpr::float32(f32::NAN)),
        },
        Kind::Bool,
        Span::dummy(),
    );
    assert_eq!(jit_eval(body), 0);
}

#[test]
fn float32_equality_is_reflexive_for_nan() {
    // The soundness-critical case: LLVM/IEEE `fcmp oeq` alone would say
    // false here, which would disagree with what the solver proves about
    // Cantor's `=` (SMT-LIB FP equality) — see `compile_binop`'s `Eq`/`Ne`
    // Float32 arm.
    let body = SemExpr::new(
        SemExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(SemExpr::float32(f32::NAN)),
            rhs: Box::new(SemExpr::float32(f32::NAN)),
        },
        Kind::Bool,
        Span::dummy(),
    );
    assert_eq!(jit_eval(body), 1);
}

#[test]
fn float32_positive_and_negative_zero_are_distinct() {
    let body = SemExpr::new(
        SemExprKind::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(SemExpr::float32(0.0)),
            rhs: Box::new(SemExpr::float32(-0.0)),
        },
        Kind::Bool,
        Span::dummy(),
    );
    assert_eq!(jit_eval(body), 0);
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
    compiler
        .compile_function("double", &[Param::new("x")], &double_body)
        .unwrap();

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
