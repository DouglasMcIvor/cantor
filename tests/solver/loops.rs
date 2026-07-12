use super::helpers::*;

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

// ── For-in over vectors (`X*`) ─────────────────────────────────────────────────
//
// Vector iteration (README "on the roadmap"): the element-hypothesis
// extraction previously only recognised `Set(ElemKind)` constructor calls in
// `constraint_env`, so a `Nat*`-constrained iterable (parameter or `mut`
// local) fell through to `Membership::Unsupported` — reported `Unknown` —
// even though codegen has supported `for x in xs` over `Vector` since the
// sequence-unification work.

#[test]
fn for_in_vector_param_proves_nat_invariant() {
    proved(
        r#"
sum : Nat* -> Nat
sum(xs) {
    mut acc: Nat = 0
    for x in xs {
        acc := acc + x
    }
    acc
}"#,
    );
}

#[test]
fn for_in_vector_param_counterexample_when_invariant_fails() {
    // acc's own invariant step fails regardless of what `x` is (acc - 10 can
    // go negative) — this only became decidable once `check_loop_inductive_step`'s
    // isolated solver got `mbqi` (see the `assign_violates_constraint_...
    // _with_unrelated_vector_param` regression test above for the root
    // cause): without it, the `∀i. nth(xs,i) ∈ Nat` domain fact for the very
    // `xs` this loop iterates was enough to make cvc5 report Unknown here.
    let src = r#"
f : Nat* -> Nat
f(xs) {
    mut acc: Nat = 5
    for x in xs {
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
fn for_in_vector_param_unknown_when_invariant_too_weak() {
    // Mirrors `for_in_unknown_when_no_constraint`: the loop's own inductive
    // step trivially holds (acc : Int is unconstrained by the loop body),
    // but that invariant is too weak to imply the function's declared Nat
    // range at loop exit.
    let src = r#"
f : Nat* -> Nat
f(xs) {
    mut acc: Int = 0
    for x in xs {
        acc := acc + x
    }
    acc
}"#;
    let results = check(src);
    assert!(
        matches!(results[0].1, CheckResult::Unknown(_)),
        "expected Unknown when loop invariant is too weak to imply the range, got {:?}",
        results[0].1
    );
}

#[test]
fn for_in_mut_local_vector_proves_nat_invariant() {
    proved(
        r#"
f : -> Nat
f() {
    mut xs: Nat* = [1, 2, 3]
    mut acc: Nat = 0
    for x in xs {
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
