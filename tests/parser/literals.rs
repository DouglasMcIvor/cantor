use cantor::ast::{BinOp, ExprKind};
use cantor::parser::parse_expr;

use super::helpers::*;

// ── Literals ──────────────────────────────────────────────────────────────────

#[test]
fn parse_int_literal() {
    assert!(matches!(parse("42"), ExprKind::IntLit(42)));
}

#[test]
fn parse_bool_true() {
    assert!(matches!(parse("true"), ExprKind::BoolLit(true)));
}

#[test]
fn parse_bool_false() {
    assert!(matches!(parse("false"), ExprKind::BoolLit(false)));
}

#[test]
fn parse_identifier() {
    assert!(matches!(parse("foo"), ExprKind::Var(sym) if sym.0 == "foo"));
}

#[test]
fn parse_char_literal() {
    assert!(matches!(parse("'a'"), ExprKind::CharLit('a')));
}

#[test]
fn parse_char_literal_escape() {
    assert!(matches!(parse(r"'\n'"), ExprKind::CharLit('\n')));
}

#[test]
fn parse_string_literal_desugars_to_tuple_of_char_lits() {
    // "cat" is sugar for a Tuple of CharLits — see `Expr::string_lit` — so
    // strings need no dedicated ExprKind of their own.
    let ExprKind::Tuple(elems) = parse("\"cat\"") else {
        panic!("expected a Tuple");
    };
    let chars: Vec<char> = elems
        .iter()
        .map(|e| match e.kind {
            ExprKind::CharLit(c) => c,
            ref other => panic!("expected CharLit, got {other:?}"),
        })
        .collect();
    assert_eq!(chars, vec!['c', 'a', 't']);
}

#[test]
fn parse_empty_string_literal_desugars_to_empty_tuple() {
    assert!(matches!(parse("\"\""), ExprKind::Tuple(elems) if elems.is_empty()));
}

#[test]
fn parse_string_concat() {
    let ExprKind::BinOp {
        op: BinOp::Concat,
        lhs,
        rhs,
    } = parse("\"Hi\" ++ \"!\"")
    else {
        panic!("expected a Concat BinOp");
    };
    assert!(matches!(lhs.kind, ExprKind::Tuple(_)));
    assert!(matches!(rhs.kind, ExprKind::Tuple(_)));
}

// ── String interpolation ─────────────────────────────────────────────────────

#[test]
fn parse_interp_string_desugars_to_concat_of_tuple_and_show_call() {
    // "a{x}b" -> ('a') ++ show(x) ++ ('b')
    let ExprKind::BinOp {
        op: BinOp::Concat,
        lhs: outer_lhs,
        rhs: outer_rhs,
    } = parse("\"a{x}b\"")
    else {
        panic!("expected a Concat BinOp");
    };
    let ExprKind::BinOp {
        op: BinOp::Concat,
        lhs: lit_a,
        rhs: show_call,
    } = &outer_lhs.kind
    else {
        panic!("expected a Concat BinOp");
    };
    assert!(matches!(&lit_a.kind, ExprKind::Tuple(elems) if elems.len() == 1));
    let ExprKind::Call { callee, args } = &show_call.kind else {
        panic!("expected a Call, got {:?}", show_call.kind);
    };
    assert_eq!(callee.0, "show");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].kind, ExprKind::Var(sym) if sym.0 == "x"));
    assert!(matches!(&outer_rhs.kind, ExprKind::Tuple(elems) if elems.len() == 1));
}

#[test]
fn parse_interp_string_with_only_an_expr_chunk_skips_empty_literal_tuples() {
    // "{x}" has no literal text at all, so it desugars straight to `show(x)`
    // — no empty Tuple(vec![])/Concat wrapping either side.
    let ExprKind::Call { callee, args } = parse("\"{x}\"") else {
        panic!("expected a bare Call");
    };
    assert_eq!(callee.0, "show");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0].kind, ExprKind::Var(sym) if sym.0 == "x"));
}

#[test]
fn parse_interp_string_multiple_chunks_left_associates() {
    // "{x}{y}" -> show(x) ++ show(y), with no empty Tuple chunk in between.
    let ExprKind::BinOp {
        op: BinOp::Concat,
        lhs,
        rhs,
    } = parse("\"{x}{y}\"")
    else {
        panic!("expected a Concat BinOp");
    };
    let ExprKind::Call { callee, args } = &lhs.kind else {
        panic!("expected lhs to be a bare Call, got {:?}", lhs.kind);
    };
    assert_eq!(callee.0, "show");
    assert!(matches!(&args[0].kind, ExprKind::Var(sym) if sym.0 == "x"));
    let ExprKind::Call { callee, args } = &rhs.kind else {
        panic!("expected rhs to be a bare Call, got {:?}", rhs.kind);
    };
    assert_eq!(callee.0, "show");
    assert!(matches!(&args[0].kind, ExprKind::Var(sym) if sym.0 == "y"));
}

#[test]
fn parse_interp_string_embedded_expr_can_be_arbitrary_expression() {
    let ExprKind::Call { callee, args } = parse("\"{1 + 2}\"") else {
        panic!("expected a bare Call");
    };
    assert_eq!(callee.0, "show");
    assert!(matches!(
        &args[0].kind,
        ExprKind::BinOp { op: BinOp::Add, .. }
    ));
}

#[test]
fn parse_interp_string_embedded_expr_span_points_into_original_source() {
    // "abc{x}" — `x` sits at byte offset 5 in the original source, not at
    // offset 0 (where it'd land if the embedded chunk's own span leaked
    // through unshifted from the fresh sub-parse).
    let expr = parse_expr("\"abc{x}\"").expect("parse error");
    let ExprKind::BinOp { rhs, .. } = expr.kind else {
        panic!("expected a Concat BinOp");
    };
    let ExprKind::Call { args, .. } = &rhs.kind else {
        panic!("expected a Call");
    };
    assert_eq!(args[0].span.start, 5);
    assert_eq!(args[0].span.end, 6);
}

#[test]
fn parse_interp_string_error_inside_embedded_expr_has_shifted_span() {
    // "abc{,}" — a bare `,` at byte offset 5 in the original source can't
    // start an expression; the resulting UnexpectedToken span must point
    // there, not at offset 0 within the extracted "," substring.
    let err = parse_expr("\"abc{,}\"").expect_err("expected a parse error");
    let cantor::error::CompileError::UnexpectedToken { span, .. } = err else {
        panic!("expected UnexpectedToken, got {err:?}");
    };
    assert_eq!(span.start, 5);
}

#[test]
fn parse_interp_string_escaped_braces_still_desugar_to_plain_tuple() {
    // No unescaped `{` at all ⇒ ordinary literal-string desugar, same as
    // `parse_string_literal_desugars_to_tuple_of_char_lits`.
    let ExprKind::Tuple(elems) = parse("\"{{a}}\"") else {
        panic!("expected a Tuple");
    };
    let chars: Vec<char> = elems
        .iter()
        .map(|e| match e.kind {
            ExprKind::CharLit(c) => c,
            ref other => panic!("expected CharLit, got {other:?}"),
        })
        .collect();
    assert_eq!(chars, vec!['{', 'a', '}']);
}

#[test]
fn parse_empty_char_literal_errors() {
    assert!(parse_err("''").contains("empty char literal"));
}

#[test]
fn parse_unterminated_char_literal_errors() {
    assert!(parse_err("'a").contains("unterminated"));
}
