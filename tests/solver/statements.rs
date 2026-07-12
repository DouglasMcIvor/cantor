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

// `check_require` (which backs `:=` reassignment checks) spins up its own
// isolated `tmp` solver seeded from every fact asserted on the main solver
// so far — including, for a function with a `Vector`-kind parameter, a
// quantified `∀i. nth(xs,i) ∈ Nat` domain fact that has nothing to do with
// this assignment at all. That `tmp` solver used to omit the `mbqi`
// (model-based quantifier instantiation) option present on every other
// solver instance in this module, so cvc5 would report `Unknown` for an
// otherwise-trivial counterexample query merely because *some* quantified
// formula was in scope. Fixed by setting `mbqi` on `check_require`'s (and
// `check_loop_inductive_step`'s, and `validate_disjoint_unions`'s) solver
// too, matching `configured_solver`/`check_name_def`.
#[test]
fn assign_violates_constraint_counterexample_with_unrelated_vector_param() {
    let results = check(
        r#"
f : Nat* -> Nat
f(xs) {
    mut acc: Nat = 5
    acc := 0 - 1
    acc
}"#,
    );
    assert!(
        matches!(results[0].1, CheckResult::Counterexample { .. }),
        "expected Counterexample (acc := -1 violates Nat) even with an unused \
         Nat* param in scope, got {:?}",
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

