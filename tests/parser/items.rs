use cantor::ast::{BinOp, DefKind, ExprKind, Item};
use cantor::parser::parse_file;

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

// ── Function parameter guards (`x for <expr>`) ─────────────────────────────────

#[test]
fn param_without_guard_has_none() {
    let items = parse_file("f : Int -> Int\nf(x) = x").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert!(def.params[0].guard.is_none());
}

#[test]
fn param_with_guard_parses_predicate() {
    let items = parse_file("sign : Int -> Int\nsign(x for x < 0) = -x").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_eq!(def.params[0].name.0, "x");
    let guard = def.params[0]
        .guard
        .as_ref()
        .unwrap_or_else(|| panic!("expected a guard on param `x`"));
    assert!(matches!(guard.kind, ExprKind::BinOp { op: BinOp::Lt, .. }));
}

#[test]
fn multi_param_guard_only_on_second_param() {
    let items = parse_file("f : Int * Int -> Int\nf(x, y for y > 0) = x + y").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert!(def.params[0].guard.is_none());
    assert!(def.params[1].guard.is_some());
}

// ── Literal-arm overloading (`f(0) = ...`) ──────────────────────────────────────

#[test]
fn literal_param_synthesizes_equality_guard() {
    let items = parse_file("factorial : Nat -> Nat\nfactorial(0) = 1").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_eq!(def.params.len(), 1);
    let guard = def.params[0]
        .guard
        .as_ref()
        .unwrap_or_else(|| panic!("expected a synthesized guard on the literal param"));
    assert!(matches!(guard.kind, ExprKind::BinOp { op: BinOp::Eq, .. }));
}

#[test]
fn two_literal_params_get_distinct_synthesized_names() {
    let items = parse_file("f : Int * Int -> Int\nf(0, 1) = 0").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_ne!(def.params[0].name.0, def.params[1].name.0);
}

// ── Named union sets (`distinct (Label: Expr | Label: Expr | ...)`) ────────────

#[test]
fn labeled_distinct_union_records_labels_in_order() {
    let (_name, kind, _rhs) = parse_name_def("Shape = distinct (Circle: Nat | Radius: NatPos)");
    assert_eq!(kind, DefKind::Distinct);
    let items = parse_file("Shape = distinct (Circle: Nat | Radius: NatPos)").unwrap();
    let Item::NameDef(ref def) = items[0] else {
        panic!("expected NameDef")
    };
    let labels = def
        .labels
        .as_ref()
        .unwrap_or_else(|| panic!("expected labels on a labeled distinct union"));
    assert_eq!(
        labels.iter().map(|s| s.0.as_str()).collect::<Vec<_>>(),
        vec!["Circle", "Radius"]
    );
}

#[test]
fn labeled_distinct_union_value_is_disjoint_union_binop() {
    // Labeled arms fold via `+` (disjoint union), not `|`, regardless of the
    // `|` separator token in source — `+` is what forces a real runtime tag
    // even when arms share a Kind (`Circle`/`Radius` are both `Kind::Int`
    // here), which labels need to mean anything at all. See
    // `parser::items::parse_distinct_value`.
    let items = parse_file("Shape = distinct (Circle: Nat | Radius: NatPos)").unwrap();
    let Item::NameDef(ref def) = items[0] else {
        panic!("expected NameDef")
    };
    assert!(matches!(
        def.value.kind,
        ExprKind::BinOp { op: BinOp::Add, .. }
    ));
}

#[test]
fn plain_distinct_has_no_labels() {
    let items = parse_file("Litre = distinct Nat").unwrap();
    let Item::NameDef(ref def) = items[0] else {
        panic!("expected NameDef")
    };
    assert!(def.labels.is_none());
}

#[test]
fn parenthesized_non_labeled_distinct_still_parses() {
    // `distinct (Meter * Meter)` — parenthesized but not a `Label: Expr` list —
    // must still parse as an ordinary set expression, not attempt the
    // labeled-arm grammar.
    let items = parse_file("Pair = distinct (Nat * Nat)").unwrap();
    let Item::NameDef(ref def) = items[0] else {
        panic!("expected NameDef")
    };
    assert!(def.labels.is_none());
    assert!(matches!(
        def.value.kind,
        ExprKind::BinOp { op: BinOp::Mul, .. }
    ));
}

#[test]
fn named_union_constructor_call_parses_as_dotted_call() {
    let items = parse_file("main : -> Int\nmain() = Shape.Circle(3)").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    let cantor::ast::FunctionBody::Expr(ref body) = def.body else {
        panic!("expected expr body")
    };
    match &body.kind {
        ExprKind::Call { callee, args } => {
            assert_eq!(callee.0, "Shape.Circle");
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Call, got {other:?}"),
    }
}

// ── Constructor patterns (pattern-matching plan, step 4/4) ─────────────────────

#[test]
fn scalar_ctor_pattern_param_records_union_label_and_binder() {
    let items = parse_file("area : Shape -> Nat\narea(Shape.Circle(r)) = r * r").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_eq!(def.params.len(), 1);
    let param = &def.params[0];
    assert_eq!(param.name.0, "__pat0");
    assert!(param.guard.is_none());
    let cp = param
        .ctor_pattern
        .as_ref()
        .unwrap_or_else(|| panic!("expected a ctor_pattern"));
    assert_eq!(cp.union_name.0, "Shape");
    assert_eq!(cp.label.0, "Circle");
    assert_eq!(
        cp.binders.iter().map(|s| s.0.as_str()).collect::<Vec<_>>(),
        vec!["r"]
    );
}

#[test]
fn tuple_ctor_pattern_param_records_multiple_binders() {
    let items = parse_file("area : Shape -> Nat\narea(Shape.Rect(x, y)) = x * y").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    let cp = def.params[0]
        .ctor_pattern
        .as_ref()
        .unwrap_or_else(|| panic!("expected a ctor_pattern"));
    assert_eq!(cp.union_name.0, "Shape");
    assert_eq!(cp.label.0, "Rect");
    assert_eq!(
        cp.binders.iter().map(|s| s.0.as_str()).collect::<Vec<_>>(),
        vec!["x", "y"]
    );
}

#[test]
fn ctor_pattern_param_index_avoids_collision_with_second_param() {
    let items = parse_file("f : Shape * Shape -> Nat\nf(Shape.Circle(r), Shape.Radius(s)) = r + s")
        .unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert_eq!(def.params[0].name.0, "__pat0");
    assert_eq!(def.params[1].name.0, "__pat1");
}

// ── Ordered guard groups (`_` wildcard + shared-signature arms) ────────────────

#[test]
fn underscore_param_sets_is_wildcard() {
    let items = parse_file("f : Int -> Int\nf(x for x < 0) = -x\nf(_) = 0").unwrap();
    let Item::FunctionDef(ref def) = items[1] else {
        panic!("expected FunctionDef")
    };
    assert!(def.params[0].is_wildcard);
    assert!(def.params[0].guard.is_none());
    assert!(def.params[0].ctor_pattern.is_none());
}

#[test]
fn two_bodies_no_repeated_sig_form_ordered_group() {
    let items = parse_file("sign : Int -> Int\nsign(x for x < 0) = -x\nsign(_) = 0").unwrap();
    assert_eq!(items.len(), 2);
    let groups: Vec<Option<u32>> = items
        .iter()
        .map(|item| {
            let Item::FunctionDef(def) = item else {
                panic!("expected FunctionDef")
            };
            def.ordered_group
        })
        .collect();
    assert!(groups[0].is_some());
    assert_eq!(groups[0], groups[1]);
}

#[test]
fn three_arm_ordered_group_all_share_one_group_id() {
    let items =
        parse_file("sign : Int -> Int\nsign(x for x < 0) = -x\nsign(x for x > 0) = x\nsign(_) = 0")
            .unwrap();
    assert_eq!(items.len(), 3);
    let ids: Vec<u32> = items
        .iter()
        .map(|item| {
            let Item::FunctionDef(def) = item else {
                panic!("expected FunctionDef")
            };
            def.ordered_group.expect("expected an ordered_group id")
        })
        .collect();
    assert_eq!(ids[0], ids[1]);
    assert_eq!(ids[1], ids[2]);
}

#[test]
fn single_body_still_has_no_ordered_group() {
    let items = parse_file("f : Int -> Int\nf(x) = x").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert!(def.ordered_group.is_none());
}

#[test]
fn repeated_sig_form_still_has_no_ordered_group() {
    // Today's disjoint-overload form: every arm restates its own signature.
    // Must NOT be mistaken for an ordered group.
    let items =
        parse_file("sign : {0} -> Int\nsign(x) = 0\nsign : Int -> Int\nsign(x for x < 0) = -x")
            .unwrap();
    assert_eq!(items.len(), 2);
    for item in &items {
        let Item::FunctionDef(def) = item else {
            panic!("expected FunctionDef")
        };
        assert!(def.ordered_group.is_none());
    }
}

#[test]
fn two_separate_ordered_groups_get_distinct_ids() {
    let items = parse_file(
        "f : Int -> Int\nf(x for x < 0) = -x\nf(_) = 0\ng : Int -> Int\ng(x for x < 0) = -x\ng(_) = 0",
    )
    .unwrap();
    let ids: Vec<u32> = items
        .iter()
        .map(|item| {
            let Item::FunctionDef(def) = item else {
                panic!("expected FunctionDef")
            };
            def.ordered_group.expect("expected an ordered_group id")
        })
        .collect();
    assert_ne!(ids[0], ids[2]);
}

#[test]
fn bare_unguarded_param_outside_group_still_legal() {
    // No group formed (only one body) — a bare param is unaffected.
    let items = parse_file("f : Int -> Int\nf(x) = x").unwrap();
    let Item::FunctionDef(ref def) = items[0] else {
        panic!("expected FunctionDef")
    };
    assert!(!def.params[0].is_wildcard);
}

#[test]
fn bare_unguarded_param_in_last_arm_of_group_is_rejected() {
    let err = parse_file("f : Int -> Int\nf(x for x < 0) = -x\nf(y) = y")
        .expect_err("expected a parse error");
    let cantor::error::CompileError::OrderedGroupBareParam { name, .. } = err else {
        panic!("expected OrderedGroupBareParam, got {err:?}");
    };
    assert_eq!(name, "f");
}

#[test]
fn bare_unguarded_param_in_first_arm_of_group_is_rejected() {
    let err = parse_file("f : Int -> Int\nf(x) = x\nf(_) = 0").expect_err("expected a parse error");
    let cantor::error::CompileError::OrderedGroupBareParam { name, .. } = err else {
        panic!("expected OrderedGroupBareParam, got {err:?}");
    };
    assert_eq!(name, "f");
}

#[test]
fn mismatched_arity_in_ordered_group_arm_is_rejected() {
    let err = parse_file("f : Int -> Int\nf(x for x < 0) = -x\nf(x, y) = x + y")
        .expect_err("expected a parse error");
    let cantor::error::CompileError::OrderedGroupArityMismatch { name, .. } = err else {
        panic!("expected OrderedGroupArityMismatch, got {err:?}");
    };
    assert_eq!(name, "f");
}
