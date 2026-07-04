use cantor::span::Symbol;
use cantor::{
    ast::{BinOp, DefKind, ExprKind, Item, UnOp},
    parser::{parse_expr, parse_file, parse_set_expr},
    span::offset_to_line_col,
};

// ── Helpers ───────────────────────────────────────────────────────────────────

fn parse(src: &str) -> ExprKind {
    parse_expr(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"))
        .kind
}

fn parse_err(src: &str) -> String {
    parse_expr(src)
        .err()
        .unwrap_or_else(|| panic!("expected parse error for {src:?}"))
        .to_string()
}

/// Walk the AST and collect BinOp operators in inorder (lhs op rhs) order.
/// Useful for checking associativity without spelling out the full AST.
fn inorder_ops(kind: &ExprKind) -> Vec<BinOp> {
    match kind {
        ExprKind::BinOp { op, lhs, rhs } => {
            let mut ops = inorder_ops(&lhs.kind);
            ops.push(*op);
            ops.extend(inorder_ops(&rhs.kind));
            ops
        }
        _ => vec![],
    }
}

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

// ── Arithmetic ────────────────────────────────────────────────────────────────

#[test]
fn parse_add() {
    assert!(matches!(
        parse("1 + 2"),
        ExprKind::BinOp { op: BinOp::Add, .. }
    ));
}

#[test]
fn parse_mul_binds_tighter_than_add() {
    // 1 + 2 * 3  →  Add(1, Mul(2, 3))
    let ExprKind::BinOp { op, rhs, .. } = parse("1 + 2 * 3") else {
        panic!()
    };
    assert_eq!(op, BinOp::Add);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::Mul, .. }));
}

#[test]
fn parse_add_is_left_assoc() {
    // 1 + 2 + 3  →  Add(Add(1, 2), 3)
    assert_eq!(
        inorder_ops(&parse("1 + 2 + 3")),
        vec![BinOp::Add, BinOp::Add]
    );
    let ExprKind::BinOp { lhs, .. } = parse("1 + 2 + 3") else {
        panic!()
    };
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn parse_parens_override_precedence() {
    // (1 + 2) * 3  →  Mul(Add(1, 2), 3)
    let ExprKind::BinOp { op, lhs, .. } = parse("(1 + 2) * 3") else {
        panic!()
    };
    assert_eq!(op, BinOp::Mul);
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn parse_unary_neg() {
    assert!(matches!(parse("-1"), ExprKind::UnOp { op: UnOp::Neg, .. }));
}

#[test]
fn parse_neg_binds_tight() {
    // -x * 2  →  Mul(Neg(x), 2)
    let ExprKind::BinOp { op, lhs, .. } = parse("-x * 2") else {
        panic!()
    };
    assert_eq!(op, BinOp::Mul);
    assert!(matches!(lhs.kind, ExprKind::UnOp { op: UnOp::Neg, .. }));
}

// ── Comparisons ───────────────────────────────────────────────────────────────

#[test]
fn parse_eq() {
    assert!(matches!(
        parse("x == y"),
        ExprKind::BinOp { op: BinOp::Eq, .. }
    ));
}

#[test]
fn parse_ne() {
    assert!(matches!(
        parse("x != y"),
        ExprKind::BinOp { op: BinOp::Ne, .. }
    ));
}

#[test]
fn parse_lt_le_gt_ge() {
    assert!(matches!(
        parse("a < b"),
        ExprKind::BinOp { op: BinOp::Lt, .. }
    ));
    assert!(matches!(
        parse("a <= b"),
        ExprKind::BinOp { op: BinOp::Le, .. }
    ));
    assert!(matches!(
        parse("a > b"),
        ExprKind::BinOp { op: BinOp::Gt, .. }
    ));
    assert!(matches!(
        parse("a >= b"),
        ExprKind::BinOp { op: BinOp::Ge, .. }
    ));
}

#[test]
fn parse_comparison_lower_than_arithmetic() {
    // 1 + 2 == 3  →  Eq(Add(1, 2), 3)
    let ExprKind::BinOp { op, lhs, .. } = parse("1 + 2 == 3") else {
        panic!()
    };
    assert_eq!(op, BinOp::Eq);
    assert!(matches!(lhs.kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

// ── Membership ────────────────────────────────────────────────────────────────

#[test]
fn parse_in() {
    assert!(matches!(
        parse("x in S"),
        ExprKind::BinOp { op: BinOp::In, .. }
    ));
}

#[test]
fn parse_not_in() {
    assert!(matches!(
        parse("x not in S"),
        ExprKind::BinOp {
            op: BinOp::NotIn,
            ..
        }
    ));
}

// ── Set operators ─────────────────────────────────────────────────────────────

#[test]
fn parse_union() {
    assert!(matches!(
        parse("A | B"),
        ExprKind::BinOp {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn parse_intersect() {
    assert!(matches!(
        parse("A & B"),
        ExprKind::BinOp {
            op: BinOp::Intersect,
            ..
        }
    ));
}

#[test]
fn parse_sym_diff() {
    assert!(matches!(
        parse("A ^ B"),
        ExprKind::BinOp {
            op: BinOp::SymDiff,
            ..
        }
    ));
}

#[test]
fn parse_set_op_precedence() {
    // A | B & C  →  Union(A, Intersect(B, C))  because & > |
    let ExprKind::BinOp { op, rhs, .. } = parse("A | B & C") else {
        panic!()
    };
    assert_eq!(op, BinOp::Union);
    assert!(matches!(
        rhs.kind,
        ExprKind::BinOp {
            op: BinOp::Intersect,
            ..
        }
    ));
}

// ── Logic ─────────────────────────────────────────────────────────────────────

#[test]
fn parse_and() {
    assert!(matches!(
        parse("a and b"),
        ExprKind::BinOp { op: BinOp::And, .. }
    ));
}

#[test]
fn parse_or() {
    assert!(matches!(
        parse("a or b"),
        ExprKind::BinOp { op: BinOp::Or, .. }
    ));
}

#[test]
fn parse_not() {
    assert!(matches!(
        parse("not x"),
        ExprKind::UnOp { op: UnOp::Not, .. }
    ));
}

#[test]
fn parse_not_absorbs_comparison() {
    // `not x == y`  →  Not(Eq(x, y))  — not does NOT steal `x` alone
    let ExprKind::UnOp { op, expr } = parse("not x == y") else {
        panic!()
    };
    assert_eq!(op, UnOp::Not);
    assert!(matches!(expr.kind, ExprKind::BinOp { op: BinOp::Eq, .. }));
}

#[test]
fn parse_not_does_not_absorb_and() {
    // `not x and y`  →  And(Not(x), y)
    let ExprKind::BinOp { op, lhs, .. } = parse("not x and y") else {
        panic!()
    };
    assert_eq!(op, BinOp::And);
    assert!(matches!(lhs.kind, ExprKind::UnOp { op: UnOp::Not, .. }));
}

#[test]
fn parse_and_tighter_than_or() {
    // a or b and c  →  Or(a, And(b, c))
    let ExprKind::BinOp { op, rhs, .. } = parse("a or b and c") else {
        panic!()
    };
    assert_eq!(op, BinOp::Or);
    assert!(matches!(rhs.kind, ExprKind::BinOp { op: BinOp::And, .. }));
}

// ── Function calls ────────────────────────────────────────────────────────────

#[test]
fn parse_call_no_args() {
    assert!(matches!(parse("f()"), ExprKind::Call { .. }));
}

#[test]
fn parse_call_one_arg() {
    let ExprKind::Call { callee, args } = parse("f(x)") else {
        panic!()
    };
    assert_eq!(callee.0, "f");
    assert_eq!(args.len(), 1);
}

#[test]
fn parse_call_multiple_args() {
    let ExprKind::Call { callee, args } = parse("add(1, 2, 3)") else {
        panic!()
    };
    assert_eq!(callee.0, "add");
    assert_eq!(args.len(), 3);
}

#[test]
fn parse_nested_call() {
    // f(g(x))
    let ExprKind::Call { args, .. } = parse("f(g(x))") else {
        panic!()
    };
    assert!(matches!(args[0].kind, ExprKind::Call { .. }));
}

#[test]
fn parse_call_in_expression() {
    // double(x) + 1
    let ExprKind::BinOp { op, lhs, .. } = parse("double(x) + 1") else {
        panic!()
    };
    assert_eq!(op, BinOp::Add);
    assert!(matches!(lhs.kind, ExprKind::Call { .. }));
}

// ── Spans ─────────────────────────────────────────────────────────────────────

#[test]
fn span_of_integer_literal() {
    let expr = parse_expr("  42  ").unwrap();
    assert_eq!(expr.span.start, 2);
    assert_eq!(expr.span.end, 4);
}

#[test]
fn span_covers_binop() {
    // "1 + 2" → span should cover the whole expression
    let expr = parse_expr("1 + 2").unwrap();
    assert_eq!(expr.span.start, 0);
    assert_eq!(expr.span.end, 5);
}

// ── Homogeneous tuple literals `[...]` ────────────────────────────────────────
// `[a, b, c]` desugars to `Tuple([a, b, c])` at parse time.
// TODO: once range inference is available, enforce that all elements belong to
// the same set X (homogeneity constraint).

#[test]
fn parse_array_lit_three_ints() {
    let kind = parse("[1, 2, 3]");
    let ExprKind::Tuple(elems) = kind else {
        panic!("expected Tuple, got {kind:?}")
    };
    assert_eq!(elems.len(), 3);
    assert!(matches!(elems[0].kind, ExprKind::IntLit(1)));
    assert!(matches!(elems[1].kind, ExprKind::IntLit(2)));
    assert!(matches!(elems[2].kind, ExprKind::IntLit(3)));
}

#[test]
fn parse_array_lit_bool_elements() {
    let kind = parse("[true, false]");
    let ExprKind::Tuple(elems) = kind else {
        panic!("expected Tuple, got {kind:?}")
    };
    assert_eq!(elems.len(), 2);
    assert!(matches!(elems[0].kind, ExprKind::BoolLit(true)));
    assert!(matches!(elems[1].kind, ExprKind::BoolLit(false)));
}

#[test]
fn parse_empty_array_lit() {
    let kind = parse("[]");
    assert!(matches!(kind, ExprKind::Tuple(elems) if elems.is_empty()));
}

// ── Bracket index `x[N]` — alias for `x.N` ───────────────────────────────────

#[test]
fn parse_bracket_index_is_proj() {
    // x[0]  →  Proj { base: Var("x"), index: 0 }
    let ExprKind::Proj { base, index } = parse("x[0]") else {
        panic!("expected Proj")
    };
    assert!(matches!(base.kind, ExprKind::Var(ref s) if s.0 == "x"));
    assert_eq!(index, 0);
}

#[test]
fn parse_bracket_index_two() {
    let ExprKind::Proj { index, .. } = parse("t[2]") else {
        panic!()
    };
    assert_eq!(index, 2);
}

#[test]
fn parse_bracket_index_on_array_lit() {
    // [1, 2, 3][1]  →  Proj { base: Tuple([1,2,3]), index: 1 }
    let ExprKind::Proj { base, index } = parse("[1, 2, 3][1]") else {
        panic!("expected Proj")
    };
    assert!(matches!(base.kind, ExprKind::Tuple(_)));
    assert_eq!(index, 1);
}

#[test]
fn parse_dot_and_bracket_are_equivalent() {
    // x.1  and  x[1]  should produce identical AST nodes (both Proj with index 1).
    let dot = parse("x.1");
    let bracket = parse("x[1]");
    // Both should be Proj with index 1; compare index rather than full AST.
    let ExprKind::Proj { index: di, .. } = dot else {
        panic!()
    };
    let ExprKind::Proj { index: bi, .. } = bracket else {
        panic!()
    };
    assert_eq!(di, bi);
}

// ── Repeated products `X * N` ─────────────────────────────────────────────────
// `Int * 3` desugars at parse time into `(Int * Int) * Int` (left-assoc).
// Desugaring happens in parse_set_expr (set positions only — in value position
// `x * 3` remains arithmetic multiplication).

fn parse_set(src: &str) -> ExprKind {
    parse_set_expr(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"))
        .kind
}

#[test]
fn parse_repeated_product_two() {
    // X * 2  →  Mul(X, X) — two Var nodes, not Mul(X, IntLit(2)).
    let ExprKind::BinOp { op, lhs, rhs } = parse_set("Int * 2") else {
        panic!()
    };
    assert_eq!(op, BinOp::Mul);
    assert!(
        matches!(lhs.kind, ExprKind::Var(ref s) if s.0 == "Int"),
        "lhs should be Int"
    );
    assert!(
        matches!(rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"),
        "rhs should be Int (desugared copy), not IntLit(2)"
    );
}

#[test]
fn parse_repeated_product_three() {
    // X * 3  →  Mul(Mul(X, X), X)  — left-associated tree of Var nodes.
    let ExprKind::BinOp {
        op: outer_op,
        lhs: outer_lhs,
        rhs: outer_rhs,
    } = parse_set("Int * 3")
    else {
        panic!()
    };
    assert_eq!(outer_op, BinOp::Mul);
    assert!(
        matches!(outer_rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"),
        "outer rhs should be Int Var"
    );
    let ExprKind::BinOp {
        op: inner_op,
        lhs: inner_lhs,
        rhs: inner_rhs,
    } = outer_lhs.kind
    else {
        panic!("lhs of outer Mul should itself be a Mul")
    };
    assert_eq!(inner_op, BinOp::Mul);
    assert!(matches!(inner_lhs.kind, ExprKind::Var(ref s) if s.0 == "Int"));
    assert!(matches!(inner_rhs.kind, ExprKind::Var(ref s) if s.0 == "Int"));
}

#[test]
fn parse_repeated_product_one_is_identity() {
    // X * 1  →  bare X (no Mul wrapper).
    let kind = parse_set("Nat * 1");
    assert!(
        matches!(kind, ExprKind::Var(ref s) if s.0 == "Nat"),
        "Nat * 1 should desugar to bare Nat; got {kind:?}"
    );
}

// ── Kleene-star set expressions `X*` ─────────────────────────────────────────

#[test]
fn parse_kleene_star_simple() {
    let kind = parse_set_expr("Nat*").unwrap().kind;
    assert!(
        matches!(kind, ExprKind::KleeneStar(ref inner) if matches!(inner.kind, ExprKind::Var(ref s) if s.0 == "Nat")),
        "Nat* should parse as KleeneStar(Var(Nat)); got {kind:?}"
    );
}

#[test]
fn parse_kleene_star_parenthesised_set() {
    let kind = parse_set_expr("(Nat - {0})*").unwrap().kind;
    assert!(
        matches!(kind, ExprKind::KleeneStar(ref inner) if matches!(inner.kind, ExprKind::BinOp { op: BinOp::Sub, .. })),
        "(Nat - {{0}})* should parse as KleeneStar(BinOp(Sub, …)); got {kind:?}"
    );
}

#[test]
fn parse_kleene_star_in_function_sig() {
    let items = parse_file("f : Nat* -> Int*\nf(xs) = 0").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    let sig = &def.sigs[0];
    assert!(
        matches!(
            sig.domain.as_ref().map(|d| &d.kind),
            Some(ExprKind::KleeneStar(_))
        ),
        "domain should be KleeneStar; got {:?}",
        sig.domain
    );
    assert!(
        matches!(&sig.range.kind, ExprKind::KleeneStar(_)),
        "range should be KleeneStar; got {:?}",
        sig.range.kind
    );
}

#[test]
fn parse_kleene_star_does_not_consume_mul_rhs() {
    // `Nat * Int` is multiplication (Int starts an expression), not Kleene star.
    let kind = parse_set_expr("Nat * Int").unwrap().kind;
    assert!(
        matches!(kind, ExprKind::BinOp { op: BinOp::Mul, .. }),
        "Nat * Int should parse as Mul, not KleeneStar; got {kind:?}"
    );
}

// ── Error cases ───────────────────────────────────────────────────────────────

#[test]
fn parse_empty_is_error() {
    assert!(!parse_err("").is_empty());
}

#[test]
fn parse_dangling_operator_is_error() {
    assert!(!parse_err("1 +").is_empty());
}

#[test]
fn parse_unmatched_paren_is_error() {
    assert!(!parse_err("(1 + 2").is_empty());
}

#[test]
fn parse_for_in_expr_is_error() {
    // bare `for` outside `{...}` is not a valid expression
    let msg = parse_err("for");
    assert!(msg.contains("for"), "expected 'for' in error: {msg}");
}

// ── offset_to_line_col ────────────────────────────────────────────────────────

#[test]
fn line_col_start_of_file() {
    assert_eq!(offset_to_line_col("hello", 0), (1, 1));
}

#[test]
fn line_col_mid_first_line() {
    //                               0123
    assert_eq!(offset_to_line_col("abcd", 2), (1, 3));
}

#[test]
fn line_col_start_of_second_line() {
    // "ab\ncd" — offset 3 is the 'c'
    assert_eq!(offset_to_line_col("ab\ncd", 3), (2, 1));
}

#[test]
fn line_col_mid_second_line() {
    // "ab\ncd" — offset 4 is the 'd'
    assert_eq!(offset_to_line_col("ab\ncd", 4), (2, 2));
}

#[test]
fn line_col_third_line() {
    // "a\nb\nc" — offset 4 is the 'c'
    assert_eq!(offset_to_line_col("a\nb\nc", 4), (3, 1));
}

#[test]
fn line_col_at_newline_char() {
    // The newline itself is on line 1, at the column after 'ab'
    assert_eq!(offset_to_line_col("ab\ncd", 2), (1, 3));
}

#[test]
fn line_col_clamped_to_end() {
    // Offset past end should clamp gracefully.
    let src = "hi";
    let (line, col) = offset_to_line_col(src, 999);
    assert_eq!(line, 1);
    assert_eq!(col, 3); // one past the last char
}

#[test]
fn line_col_parse_error_location() {
    use cantor::parser::parse_file;
    // "f : Int -> Int\nf(x) = @@@"
    // '@' is at line 2, column 8
    let src = "f : Int -> Int\nf(x) = @@@";
    let err = parse_file(src).unwrap_err();
    assert_eq!(err.location(src), Some((2, 8)));
}

// ── Set comprehensions ────────────────────────────────────────────────────────

#[test]
fn comprehension_no_filter() {
    let kind = parse("{x * 2 for x in {1, 3, 5}}");
    let ExprKind::Comprehension {
        output,
        var,
        source,
        filter,
    } = kind
    else {
        panic!("expected Comprehension, got {kind:?}");
    };
    assert!(matches!(
        output.kind,
        ExprKind::BinOp { op: BinOp::Mul, .. }
    ));
    assert_eq!(var, Symbol::new("x"));
    assert!(matches!(source.kind, ExprKind::SetLit(_)));
    assert!(filter.is_none());
}

#[test]
fn comprehension_with_filter() {
    let kind = parse("{x for x in {1, 2, 3, 4, 5} if x > 2}");
    let ExprKind::Comprehension {
        output,
        var,
        source,
        filter,
    } = kind
    else {
        panic!("expected Comprehension, got {kind:?}");
    };
    assert!(matches!(output.kind, ExprKind::Var(s) if s.0 == "x"));
    assert_eq!(var, Symbol::new("x"));
    assert!(matches!(source.kind, ExprKind::SetLit(_)));
    assert!(filter.is_some());
    assert!(matches!(
        filter.unwrap().kind,
        ExprKind::BinOp { op: BinOp::Gt, .. }
    ));
}

#[test]
fn comprehension_named_source() {
    // Source can be a named set (like Nat) — generative set at compile time.
    let kind = parse("{x for x in Nat if x > 0}");
    let ExprKind::Comprehension { source, .. } = kind else {
        panic!("expected Comprehension");
    };
    assert!(matches!(source.kind, ExprKind::Var(s) if s.0 == "Nat"));
}

#[test]
fn comprehension_vs_set_literal_disambiguation() {
    // {1, 2, 3} is a set literal, not a comprehension.
    assert!(matches!(parse("{1, 2, 3}"), ExprKind::SetLit(_)));
    // {x * 2 for x in S} is a comprehension.
    assert!(matches!(
        parse("{x * 2 for x in {1}}"),
        ExprKind::Comprehension { .. }
    ));
}

#[test]
fn empty_set_literal_still_works() {
    assert!(matches!(parse("{}"), ExprKind::SetLit(elems) if elems.is_empty()));
}

#[test]
fn comprehension_display_round_trips() {
    use cantor::ast::Expr;
    let comp = Expr::comprehension(
        Expr::binop(BinOp::Mul, Expr::var("x"), Expr::int(2)),
        "x",
        Expr::set_lit(vec![Expr::int(1), Expr::int(3)]),
        None,
    );
    assert_eq!(format!("{comp}"), "{x * 2 for x in {1, 3}}");
}

#[test]
fn comprehension_display_with_filter() {
    use cantor::ast::Expr;
    let comp = Expr::comprehension(
        Expr::var("x"),
        "x",
        Expr::set_lit(vec![Expr::int(1), Expr::int(2), Expr::int(3)]),
        Some(Expr::binop(BinOp::Gt, Expr::var("x"), Expr::int(1))),
    );
    assert_eq!(format!("{comp}"), "{x for x in {1, 2, 3} if x > 1}");
}

// ── Set definitions ───────────────────────────────────────────────────────────

fn parse_name_def(src: &str) -> (String, DefKind, ExprKind) {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    match items.into_iter().next().unwrap() {
        Item::NameDef(def) => (def.name.0, def.kind, def.value.kind),
        other => panic!("expected NameDef, got {other:?}"),
    }
}

#[test]
fn set_def_set_literal_implicit_alias() {
    let (name, kind, _rhs) = parse_name_def("Colour = {1, 2, 3}");
    assert_eq!(name, "Colour");
    assert_eq!(kind, DefKind::Alias);
}

#[test]
fn set_def_union_implicit_alias() {
    let (name, kind, rhs) = parse_name_def("Animal = Cat | Dog");
    assert_eq!(name, "Animal");
    assert_eq!(kind, DefKind::Alias);
    assert!(matches!(
        rhs,
        ExprKind::BinOp {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn set_def_explicit_alias_keyword() {
    let (name, kind, rhs) = parse_name_def("Animal = alias Cat | Dog");
    assert_eq!(name, "Animal");
    assert_eq!(kind, DefKind::Alias);
    assert!(matches!(
        rhs,
        ExprKind::BinOp {
            op: BinOp::Union,
            ..
        }
    ));
}

#[test]
fn set_def_distinct_keyword() {
    let (name, kind, rhs) = parse_name_def("Litre = distinct Float");
    assert_eq!(name, "Litre");
    assert_eq!(kind, DefKind::Distinct);
    assert!(matches!(rhs, ExprKind::Var(s) if s.0 == "Float"));
}

#[test]
fn set_def_distinct_set_difference() {
    let (name, kind, _rhs) = parse_name_def("SafeDiv = distinct Int - {0}");
    assert_eq!(name, "SafeDiv");
    assert_eq!(kind, DefKind::Distinct);
}

#[test]
fn set_def_alias_named_set() {
    let (name, kind, rhs) = parse_name_def("MyNat = alias Nat");
    assert_eq!(name, "MyNat");
    assert_eq!(kind, DefKind::Alias);
    assert!(matches!(rhs, ExprKind::Var(s) if s.0 == "Nat"));
}

// ── Tuple tests ───────────────────────────────────────────────────────────────

#[test]
fn tuple_literal_two_elements() {
    let kind = parse("(1, 2)");
    assert!(matches!(&kind, ExprKind::Tuple(elems) if elems.len() == 2));
    if let ExprKind::Tuple(elems) = &kind {
        assert!(matches!(&elems[0].kind, ExprKind::IntLit(1)));
        assert!(matches!(&elems[1].kind, ExprKind::IntLit(2)));
    }
}

#[test]
fn tuple_literal_three_elements() {
    let kind = parse("(1, 2, 3)");
    assert!(matches!(&kind, ExprKind::Tuple(elems) if elems.len() == 3));
}

#[test]
fn paren_grouping_unchanged() {
    let kind = parse("(1 + 2)");
    assert!(matches!(&kind, ExprKind::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn nested_tuple() {
    let kind = parse("(1, (2, 3))");
    if let ExprKind::Tuple(elems) = &kind {
        assert_eq!(elems.len(), 2);
        assert!(matches!(&elems[1].kind, ExprKind::Tuple(inner) if inner.len() == 2));
    } else {
        panic!("expected Tuple, got {kind:?}");
    }
}

#[test]
fn proj_simple() {
    let kind = parse("t.0");
    assert!(matches!(&kind, ExprKind::Proj { index: 0, .. }));
}

#[test]
fn proj_chained() {
    let kind = parse("t.0.1");
    if let ExprKind::Proj { base, index: 1 } = &kind {
        assert!(matches!(&base.kind, ExprKind::Proj { index: 0, .. }));
    } else {
        panic!("expected chained Proj, got {kind:?}");
    }
}

#[test]
fn proj_on_call() {
    let kind = parse("f(x).0");
    assert!(matches!(&kind, ExprKind::Proj { index: 0, .. }));
}

#[test]
fn tuple_display_round_trips() {
    let parsed = parse("(1, 2)");
    let displayed = format!("{parsed}");
    assert_eq!(displayed, "(1, 2)");
}

#[test]
fn proj_display_round_trips() {
    let parsed = parse("t.1");
    let displayed = format!("{parsed}");
    assert_eq!(displayed, "t.1");
}
