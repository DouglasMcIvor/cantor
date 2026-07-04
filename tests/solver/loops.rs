use super::helpers::*;

// ── Block body: assume ────────────────────────────────────────────────────────

#[test]
fn assume_narrows_domain_proved() {
    proved(
        "
f : Int -> Int
f(x) {
    assume x in Nat
    x
}
",
    );
}

#[test]
fn assume_enables_downstream_proof() {
    proved(
        "
non_neg : Int -> Nat
non_neg(x) {
    assume x in Nat
    x
}
",
    );
}

#[test]
fn assume_boolean_pred_proved() {
    proved(
        "
pred : Int -> Nat
pred(x) {
    assume x > 0
    x - 1
}
",
    );
}

#[test]
fn block_simple_let_proved() {
    proved(
        "
double : Nat -> Nat
double(x) {
    mut y: Nat = x + x
    y
}
",
    );
}

#[test]
fn block_sequential_lets_proved() {
    proved(
        "
triple : Nat -> Nat
triple(x) {
    mut y: Nat = x + x
    mut z: Nat = y + x
    z
}
",
    );
}

#[test]
fn block_range_violation_counterexample() {
    counterexample(
        "
bad : Int -> Nat
bad(x) {
    x
}
",
    );
}

// ── Reassignment (`:=`) outside loops ────────────────────────────────────────

#[test]
fn assign_valid_constraint_proved() {
    proved(
        r#"
f : Nat -> Nat
f(x) {
    mut acc: Nat = 0
    acc := x
    acc
}"#,
    );
}

#[test]
fn assign_violates_constraint_counterexample() {
    let results = check(
        r#"
f : -> Nat
f() {
    mut acc: Nat = 5
    acc := 0 - 1
    acc
}"#,
    );
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (acc := -1 violates Nat), got {:?}",
        results[0].1
    );
}

#[test]
fn assign_constraint_narrower_than_range_still_enforced() {
    // Even though the function range is Int (permissive), the declared
    // Nat constraint on `acc` must be checked at the := site.
    let results = check(
        r#"
f : -> Int
f() {
    mut acc: Nat = 5
    acc := 0 - 1
    acc
}"#,
    );
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (acc := -1 violates Nat constraint), got {:?}",
        results[0].1
    );
}

#[test]
fn assign_sequential_stays_in_nat_proved() {
    // 2 → 1 → 0: each step stays in Nat, SSA gives the solver concrete equalities.
    proved(
        r#"
f : -> Nat
f() {
    mut acc: Nat = 2
    acc := acc - 1
    acc := acc - 1
    acc
}"#,
    );
}

#[test]
fn assign_sequential_leaves_nat_counterexample() {
    // 1 → 0 → -1: the second subtraction violates the Nat constraint.
    let results = check(
        r#"
f : -> Nat
f() {
    mut acc: Nat = 1
    acc := acc - 1
    acc := acc - 1
    acc
}"#,
    );
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (second := takes acc to -1), got {:?}",
        results[0].1
    );
}

// ── Block body: require ───────────────────────────────────────────────────────

#[test]
fn require_membership_proved() {
    proved(
        "
f : NatPos -> NatPos
f(x) {
    require x in NatPos
    x
}
",
    );
}

#[test]
fn require_boolean_pred_proved() {
    proved(
        "
g : NatPos -> Nat
g(x) {
    require x > 0
    x - 1
}
",
    );
}

#[test]
fn require_enables_downstream_proof() {
    proved(
        "
safe_pred : NatPos -> Nat
safe_pred(x) {
    require x in NatPos
    x - 1
}
",
    );
}

#[test]
fn require_fails_counterexample() {
    let results = check(
        "
h : Int -> Int
h(x) {
    require x in NatPos
    x
}
",
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "requirement failed");
}

#[test]
fn require_after_assume_proved() {
    proved(
        "
chain : Int -> Nat
chain(x) {
    assume x in Nat
    require x in Nat
    x
}
",
    );
}

#[test]
fn require_division_safety_proved() {
    proved(
        "
safe_recip : NatPos -> Int
safe_recip(x) {
    require x in NonZeroInt
    1 / x
}
",
    );
}

#[test]
fn require_int_domain_fails() {
    let results = check(
        "
bad_recip : Int -> Int
bad_recip(x) {
    require x in NonZeroInt
    1 / x
}
",
    );
    let (_, result) = results.into_iter().next().unwrap();
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "require with Int domain should give counterexample, got {result:?}"
    );
}

#[test]
fn require_after_call_uses_callee_contract_proved() {
    // check_require used to run in a fresh solver seeded only from a
    // separately-threaded fact vector, which never saw call contracts —
    // those are asserted straight onto the main solver by
    // `assert_call_contract`. A `require` depending on a prior call's
    // result used to get a spurious counterexample; now check_require
    // seeds from the main solver's own assertions and sees it.
    proved_all(
        "
non_neg : Int -> Nat
non_neg(x) = if x >= 0 then x else -x

after_call : Int -> Nat
after_call(x) {
    y : Nat = non_neg(x)
    require y in Nat
    y
}
",
    );
}

#[test]
fn require_after_call_domain_gated_proved() {
    // Same bug, but with a genuinely implication-form contract:
    // `n ∈ Nat → m ∈ NatPos` only fires given the antecedent, which is
    // itself supplied by the caller's own domain — so the require can only
    // be proved by combining both the call's contract *and* the domain fact.
    proved_all(
        "
classify : Nat -> NatPos
classify(n) = n + 1

after_call_range : Nat -> NatPos
after_call_range(n) {
    m : NatPos = classify(n)
    require m in NatPos
    m
}
",
    );
}

// ── Block body: assert ────────────────────────────────────────────────────────

#[test]
fn assert_proved_statically() {
    proved(
        "
f : NatPos -> NatPos | Fail
f(x) {
    assert x in NatPos
    x
}
",
    );
}

#[test]
fn assert_always_false_counterexample() {
    let results = check(
        "
always_fails : Int -> Int | Fail
always_fails(x) {
    assert false
    x
}
",
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "assertion always fails");
}

#[test]
fn assert_unknown_enables_downstream_proof() {
    proved(
        "
safe_to_nat : Int -> Nat | Fail
safe_to_nat(x) {
    assert x in Nat
    x
}
",
    );
}

#[test]
fn assert_enables_division_safety() {
    proved(
        "
safe_recip : Int -> Int | Fail
safe_recip(x) {
    assert x in NonZeroInt
    1 / x
}
",
    );
}

#[test]
fn assert_in_infallible_function_is_counterexample() {
    // An unproven assert in a function without `| Fail` in the range is a
    // counterexample: the function can crash at runtime with no Fail path.
    let results = check(
        "
runtime_div : Int * Int -> Int
runtime_div(x, y) {
    assert y != 0
    x / y
}
",
    );
    let (label, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample for `{label}`, got {result:?}");
    };
    assert!(
        reason.contains("Fail"),
        "reason should mention `Fail`: {reason}"
    );
}

#[test]
fn assert_after_let_proved() {
    proved(
        "
bounded : Int -> Nat | Fail
bounded(x) {
    mut y: Int = x + 1
    assert y > 0
    y
}
",
    );
}

// ── While loops ───────────────────────────────────────────────────────────────

#[test]
fn while_loop_proved_with_constraints() {
    proved(
        r#"
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc := acc + i
        i := i + 1
    }
    acc
}"#,
    );
}

#[test]
fn while_loop_counterexample_when_range_tighter_than_invariant() {
    let src = r#"
sum_to_pos : Nat -> NatPos
sum_to_pos(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc := acc + i
        i := i + 1
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (n=0 → acc=0 ∉ NatPos), got {:?}",
        results[0].1
    );
}

#[test]
fn while_loop_unknown_when_var_has_no_constraint() {
    let src = r#"
f : Int -> Nat
f(n) {
    mut acc: Int = 0
    while acc < n {
        acc := acc + 1
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Unknown(_)),
        "expected Unknown when loop var has no effective constraint, got {:?}",
        results[0].1
    );
}

#[test]
fn while_loop_proved_with_assume() {
    proved(
        r#"
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc := acc + i
        i := i + 1
    }
    assume acc in Nat
    acc
}"#,
    );
}

#[test]
fn while_exit_condition_asserted() {
    proved(
        r#"
f : Nat -> Nat
f(n) {
    mut i: Nat = 0
    while i < n {
        i := i + 1
    }
    i
}"#,
    );
}

// ── Inductive step verification ───────────────────────────────────────────────

#[test]
fn inductive_step_proved_for_nat_invariant() {
    proved(
        r#"
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0
    mut i: Nat = 1
    while i <= n {
        acc := acc + i
        i := i + 1
    }
    acc
}"#,
    );
}

#[test]
fn inductive_step_fails_for_int16_overflow() {
    let src = r#"
count : Nat -> Int16
count(n) {
    mut acc: Int16 = 0
    while acc < n {
        acc := acc + 1
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { ref reason, .. }
            if reason.contains("Int16")),
        "expected Counterexample citing Int16, got {:?}",
        results[0].1
    );
}

#[test]
fn inductive_step_fails_reports_function_params() {
    let src = r#"
bounded_add : Int16 -> Int16
bounded_add(x) {
    mut acc: Int16 = x
    while true {
        acc := acc + 1
    }
    acc
}"#;
    let results = check(src);
    let CheckResult::Counterexample { ref params, .. } = results[0].1 else {
        panic!("expected Counterexample, got {:?}", results[0].1);
    };
    assert!(
        params.contains_key("x"),
        "expected param `x` in counterexample: {params:?}"
    );
}

// ── For-in loops ──────────────────────────────────────────────────────────────

#[test]
fn for_in_proved_with_constraint() {
    proved(
        r#"
sum_set : -> Nat
sum_set() {
    mut acc: Nat = 0
    for x in {1, 2, 3} {
        acc := acc + x
    }
    acc
}"#,
    );
}

#[test]
fn for_in_counterexample_when_invariant_fails() {
    let src = r#"
f : -> Nat
f() {
    mut acc: Nat = 5
    for x in {1, 2, 3} {
        acc := acc - 10
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (acc - 10 ∉ Nat), got {:?}",
        results[0].1
    );
}

#[test]
fn for_in_unknown_when_no_constraint() {
    let src = r#"
f : -> Nat
f() {
    mut acc: Int = 0
    for x in {1, 2, 3} {
        acc := acc + x
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Unknown(_)),
        "expected Unknown when loop var has no effective constraint, got {:?}",
        results[0].1
    );
}

#[test]
fn for_in_empty_set_proved() {
    proved(
        r#"
f : -> Nat
f() {
    mut acc: Nat = 0
    for x in {} {
        acc := acc + x
    }
    acc
}"#,
    );
}

#[test]
fn for_in_set_literal_with_param() {
    proved(
        r#"
f : Nat -> Nat
f(n) {
    mut acc: Nat = 0
    for x in {1, 2, 3} {
        acc := acc + x
    }
    acc
}"#,
    );
}

// ── Loop-body built-in obligations ────────────────────────────────────────────
//
// Obligations produced while encoding a loop body (division domains, call-site
// domains, unproved asserts, …) are checked under the induction hypothesis —
// previously they were collected and dropped, so a proved function could
// divide by zero at runtime.

#[test]
fn loop_body_division_by_zero_counterexample() {
    let results = check(
        r#"
f : Nat -> Nat
f(n) {
    mut i: Nat = 0
    while i < n {
        i := i + 10 / i
    }
    i
}"#,
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "division by zero");
}

#[test]
fn loop_body_division_feeding_unconstrained_var_counterexample() {
    // The obligation must be checked even when the divided value only feeds a
    // variable whose invariant (`Int`) imposes no constraint — nothing else
    // in the query would surface it.
    let results = check(
        r#"
h : Nat -> Nat
h(n) {
    mut i: Nat = 0
    mut junk: Int = 0
    while i < n {
        junk := 10 / (n - n)
        i := i + 1
    }
    i
}"#,
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "division by zero");
}

#[test]
fn loop_body_division_safe_from_invariant_proved() {
    // The obligation is discharged using the hypothesis: i ∈ Nat → i + 1 ≠ 0.
    proved(
        r#"
f : Nat -> Nat
f(n) {
    mut i: Nat = 0
    mut acc: Nat = 0
    while i < n {
        acc := acc + 10 / (i + 1)
        i := i + 1
    }
    acc
}"#,
    );
}

#[test]
fn loop_body_call_domain_violation_counterexample() {
    let results = check_all(
        r#"
half : Nat -> Nat
half(x) = x / 2

f : Nat -> Nat
f(n) {
    mut i: Nat = 0
    mut acc: Nat = 0
    while i < n {
        acc := acc + half(i - 1)
        i := i + 1
    }
    acc
}"#,
    );
    let CheckResult::Counterexample { reason, .. } = result_for(&results, "f") else {
        panic!("expected counterexample for f");
    };
    assert!(
        reason.contains("not in its declared domain"),
        "reason should name the call-site domain violation: {reason}"
    );
}

#[test]
fn loop_body_call_in_domain_proved() {
    proved_all(
        r#"
half : Nat -> Nat
half(x) = x / 2

f : Nat -> Nat
f(n) {
    mut i: Nat = 0
    mut acc: Nat = 0
    while i < n {
        acc := acc + half(i)
        i := i + 1
    }
    acc
}"#,
    );
}

#[test]
fn loop_body_require_uses_pre_loop_call_contract_proved() {
    // Same root cause as `require_after_call_uses_callee_contract_proved`,
    // but for the loop inductive-step checker: the call happens *before* the
    // loop, so its contract lives only on the outer solver. The inductive
    // step used to build its own fresh solver seeded from a separately
    // threaded fact vector that never saw it, so `require y in Nat` inside
    // the body would get a spurious counterexample.
    proved_all(
        r#"
non_neg : Int -> Nat
non_neg(x) = if x >= 0 then x else -x

f : Int -> Nat
f(x) {
    y : Nat = non_neg(x)
    mut i: Nat = 0
    while i < 3 {
        require y in Nat
        i := i + 1
    }
    y
}"#,
    );
}

#[test]
fn loop_body_runtime_assert_needs_fail_counterexample() {
    // An unproved assert inside a loop body compiles to a runtime check, so
    // the range must declare `| Fail` — the flag must not be lost in the
    // induction path.
    let results = check(
        r#"
f : Int -> Int
f(x) {
    mut i: Int = 0
    while i < x {
        assert i < 1000
        i := i + 1
    }
    i
}"#,
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert!(
        reason.contains("does not include `Fail`"),
        "reason should demand | Fail: {reason}"
    );
}

#[test]
fn loop_body_runtime_assert_with_fail_range_proved() {
    proved(
        r#"
f : Int -> Int | Fail
f(x) {
    mut i: Int = 0
    while i < x {
        assert i < 1000
        i := i + 1
    }
    i
}"#,
    );
}

#[test]
fn for_in_body_division_by_zero_counterexample() {
    let results = check(
        r#"
f : -> Nat
f() {
    mut acc: Nat = 0
    for x in {0, 1, 2} {
        acc := acc + 10 / x
    }
    acc
}"#,
    );
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample, got {result:?}");
    };
    assert_eq!(reason, "division by zero");
}

#[test]
fn for_in_body_division_nonzero_elements_proved() {
    proved(
        r#"
f : -> Nat
f() {
    mut acc: Nat = 0
    for x in {1, 2, 5} {
        acc := acc + 10 / x
    }
    acc
}"#,
    );
}

// ── Non-integer mutables crossing a loop ──────────────────────────────────────
//
// Post-loop havoc constants and induction-hypothesis variables take the sort
// of the value they shadow; a mutable Bool crossing a `while` used to become
// an integer-sorted fresh constant and abort cvc5.

#[test]
fn while_loop_mut_bool_proved() {
    proved(
        "
f : Nat -> Bool
f(n) {
    mut flag: Bool = true
    mut i: Nat = 0
    while i < n {
        flag := not flag
        i := i + 1
    }
    flag
}
",
    );
}
