use super::helpers::*;

// ── Block body: assume ────────────────────────────────────────────────────────

#[test]
fn assume_narrows_domain_proved() {
    proved("
f : Int -> Int
f(x) {
    assume x in Nat
    x
}
");
}

#[test]
fn assume_enables_downstream_proof() {
    proved("
non_neg : Int -> Nat
non_neg(x) {
    assume x in Nat
    x
}
");
}

#[test]
fn assume_boolean_pred_proved() {
    proved("
pred : Int -> Nat
pred(x) {
    assume x > 0
    x - 1
}
");
}

#[test]
fn block_simple_let_proved() {
    proved("
double : Nat -> Nat
double(x) {
    mut y: Nat = x + x
    y
}
");
}

#[test]
fn block_sequential_lets_proved() {
    proved("
triple : Nat -> Nat
triple(x) {
    mut y: Nat = x + x
    mut z: Nat = y + x
    z
}
");
}

#[test]
fn block_range_violation_counterexample() {
    counterexample("
bad : Int -> Nat
bad(x) {
    x
}
");
}

// ── Block body: require ───────────────────────────────────────────────────────

#[test]
fn require_membership_proved() {
    proved("
f : NatPos -> NatPos
f(x) {
    require x in NatPos
    x
}
");
}

#[test]
fn require_boolean_pred_proved() {
    proved("
g : NatPos -> Nat
g(x) {
    require x > 0
    x - 1
}
");
}

#[test]
fn require_enables_downstream_proof() {
    proved("
safe_pred : NatPos -> Nat
safe_pred(x) {
    require x in NatPos
    x - 1
}
");
}

#[test]
fn require_fails_counterexample() {
    let results = check("
h : Int -> Int
h(x) {
    require x in NatPos
    x
}
");
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "requirement failed");
}

#[test]
fn require_after_assume_proved() {
    proved("
chain : Int -> Nat
chain(x) {
    assume x in Nat
    require x in Nat
    x
}
");
}

#[test]
fn require_division_safety_proved() {
    proved("
safe_recip : NatPos -> Int
safe_recip(x) {
    require x in NonZeroInt
    1 / x
}
");
}

#[test]
fn require_int_domain_fails() {
    let results = check("
bad_recip : Int -> Int
bad_recip(x) {
    require x in NonZeroInt
    1 / x
}
");
    let (_, result) = results.into_iter().next().unwrap();
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "require with Int domain should give counterexample, got {result:?}"
    );
}

// ── Block body: assert ────────────────────────────────────────────────────────

#[test]
fn assert_proved_statically() {
    proved("
f : NatPos -> NatPos | Fail
f(x) {
    assert x in NatPos
    x
}
");
}

#[test]
fn assert_always_false_counterexample() {
    let results = check("
always_fails : Int -> Int | Fail
always_fails(x) {
    assert false
    x
}
");
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "assertion always fails");
}

#[test]
fn assert_unknown_enables_downstream_proof() {
    proved("
safe_to_nat : Int -> Nat | Fail
safe_to_nat(x) {
    assert x in Nat
    x
}
");
}

#[test]
fn assert_enables_division_safety() {
    proved("
safe_recip : Int -> Int | Fail
safe_recip(x) {
    assert x in NonZeroInt
    1 / x
}
");
}

#[test]
fn assert_in_infallible_function_is_counterexample() {
    // An unproven assert in a function without `| Fail` in the range is a
    // counterexample: the function can crash at runtime with no Fail path.
    let results = check("
runtime_div : Int * Int -> Int
runtime_div(x, y) {
    assert y != 0
    x / y
}
");
    let (label, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample for `{label}`, got {result:?}");
    };
    assert!(reason.contains("Fail"), "reason should mention `Fail`: {reason}");
}

#[test]
fn assert_after_let_proved() {
    proved("
bounded : Int -> Nat | Fail
bounded(x) {
    mut y: Int = x + 1
    assert y > 0
    y
}
");
}

// ── While loops ───────────────────────────────────────────────────────────────

#[test]
fn while_loop_proved_with_constraints() {
    proved(r#"
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc = acc + i
        i = i + 1
    }
    acc
}"#);
}

#[test]
fn while_loop_counterexample_when_range_tighter_than_invariant() {
    let src = r#"
sum_to_pos : Nat -> NatPos
sum_to_pos(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc = acc + i
        i = i + 1
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (n=0 → acc=0 ∉ NatPos), got {:?}", results[0].1
    );
}

#[test]
fn while_loop_unknown_when_var_has_no_constraint() {
    let src = r#"
f : Int -> Nat
f(n) {
    mut acc: Int = 0
    while acc < n {
        acc = acc + 1
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Unknown(_)),
        "expected Unknown when loop var has no effective constraint, got {:?}", results[0].1
    );
}

#[test]
fn while_loop_proved_with_assume() {
    proved(r#"
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc = acc + i
        i = i + 1
    }
    assume acc in Nat
    acc
}"#);
}

#[test]
fn while_exit_condition_asserted() {
    proved(r#"
f : Nat -> Nat
f(n) {
    mut i: Nat = 0
    while i < n {
        i = i + 1
    }
    i
}"#);
}

// ── Inductive step verification ───────────────────────────────────────────────

#[test]
fn inductive_step_proved_for_nat_invariant() {
    proved(r#"
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc = acc + i
        i = i + 1
    }
    acc
}"#);
}

#[test]
fn inductive_step_fails_for_int16_overflow() {
    let src = r#"
count : Nat -> Int16
count(n) {
    mut acc: Int16 = 0
    while acc < n {
        acc = acc + 1
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { ref reason, .. }
            if reason.contains("Int16")),
        "expected Counterexample citing Int16, got {:?}", results[0].1
    );
}

#[test]
fn inductive_step_fails_reports_function_params() {
    let src = r#"
bounded_add : Int16 -> Int16
bounded_add(x) {
    mut acc: Int16 = x
    while true {
        acc = acc + 1
    }
    acc
}"#;
    let results = check(src);
    let CheckResult::Counterexample { ref params, .. } = results[0].1 else {
        panic!("expected Counterexample, got {:?}", results[0].1);
    };
    assert!(params.contains_key("x"), "expected param `x` in counterexample: {params:?}");
}

// ── For-in loops ──────────────────────────────────────────────────────────────

#[test]
fn for_in_proved_with_constraint() {
    proved(r#"
sum_set : -> Nat
sum_set() {
    mut acc: Nat = 0
    for x in {1, 2, 3} {
        acc = acc + x
    }
    acc
}"#);
}

#[test]
fn for_in_counterexample_when_invariant_fails() {
    let src = r#"
f : -> Nat
f() {
    mut acc: Nat = 5
    for x in {1, 2, 3} {
        acc = acc - 10
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (acc - 10 ∉ Nat), got {:?}", results[0].1
    );
}

#[test]
fn for_in_unknown_when_no_constraint() {
    let src = r#"
f : -> Nat
f() {
    mut acc: Int = 0
    for x in {1, 2, 3} {
        acc = acc + x
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Unknown(_)),
        "expected Unknown when loop var has no effective constraint, got {:?}", results[0].1
    );
}

#[test]
fn for_in_empty_set_proved() {
    proved(r#"
f : -> Nat
f() {
    mut acc: Nat = 0
    for x in {} {
        acc = acc + x
    }
    acc
}"#);
}

#[test]
fn for_in_set_literal_with_param() {
    proved(r#"
f : Nat -> Nat
f(n) {
    mut acc: Nat = 0
    for x in {1, 2, 3} {
        acc = acc + x
    }
    acc
}"#);
}
