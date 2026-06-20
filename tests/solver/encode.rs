use super::helpers::*;

// ── Identity and trivial ──────────────────────────────────────────────────────

#[test]
fn identity_int_to_int() {
    proved("f : Int -> Int\nf(x) = x");
}

#[test]
fn constant_zero_nat() {
    proved("zero : -> Nat\nzero() = 0");
}

// ── abs ───────────────────────────────────────────────────────────────────────

#[test]
fn abs_int_to_nat() {
    proved("abs : Int -> Nat\nabs(x) = if x >= 0 then x else -x");
}

// ── Arithmetic range proofs ───────────────────────────────────────────────────

#[test]
fn double_nat_to_nat() {
    proved("double : Nat -> Nat\ndouble(x) = x + x");
}

#[test]
fn add_nats_is_nat() {
    proved("add : Nat * Nat -> Nat\nadd(x, y) = x + y");
}

#[test]
fn natpos_plus_natpos_is_natpos() {
    proved("add_pos : NatPos * NatPos -> NatPos\nadd_pos(x, y) = x + y");
}

// ── Counterexamples ───────────────────────────────────────────────────────────

#[test]
fn identity_not_natpos() {
    counterexample("f : Int -> NatPos\nf(x) = x");
}

#[test]
fn subtraction_breaks_nat() {
    counterexample("f : Nat -> Nat\nf(x) = x - 1");
}

#[test]
fn negation_breaks_nat() {
    counterexample("neg : Int -> Nat\nneg(x) = -x");
}

// ── Multiple signatures ───────────────────────────────────────────────────────

#[test]
fn abs_two_sigs_both_proved() {
    let src = "abs : Nat -> Nat\nabs : Int -> Nat\nabs(x) = if x >= 0 then x else -x";
    for (label, result) in &check(src) {
        assert_eq!(result, &CheckResult::Proved, "`{label}` should be Proved");
    }
}

// ── Zero-arg functions ────────────────────────────────────────────────────────

#[test]
fn zero_arg_constant_nat() {
    proved("answer : -> Nat\nanswer() = 42");
}

#[test]
fn zero_arg_negative_not_nat() {
    counterexample("bad : -> Nat\nbad() = -1");
}

// ── Interprocedural: single call ──────────────────────────────────────────────

#[test]
fn double_then_quad_both_proved() {
    let src = "
double : Nat -> Nat
double(x) = x + x

quad : Nat -> Nat
quad(x) = double(double(x))
";
    for (_fn_name, sig_results) in check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, CheckResult::Proved, "`{label}` should be Proved");
        }
    }
}

#[test]
fn caller_proved_via_callee_contract() {
    let src = "
succ_nat : Nat -> NatPos
succ_nat(x) = x + 1

wrap_succ : Nat -> NatPos
wrap_succ(x) = succ_nat(x)
";
    for (_fn_name, sig_results) in check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, CheckResult::Proved, "`{label}` should be Proved");
        }
    }
}

#[test]
fn caller_refuted_when_callee_range_too_weak() {
    let src = "
negate : Nat -> Int
negate(x) = -x

caller : Nat -> Nat
caller(x) = negate(x)
";
    let all = check_all(src);
    let negate_result = all.iter().find(|(n, _)| n == "negate").unwrap();
    assert_eq!(negate_result.1[0].1, CheckResult::Proved);
    let caller_result = all.iter().find(|(n, _)| n == "caller").unwrap();
    assert!(
        matches!(caller_result.1[0].1, CheckResult::Counterexample { .. }),
        "caller should be Counterexample, got {:?}", caller_result.1[0].1
    );
}

#[test]
fn recursive_function_proved_via_own_contract() {
    proved("
factorial : NatPos -> NatPos
factorial(n) = if n == 1 then 1 else n * factorial(n - 1)
");
}

// ── Interprocedural: two-argument callee ─────────────────────────────────────

#[test]
fn two_arg_callee_contract() {
    let src = "
add_nat : Nat * Nat -> Nat
add_nat(x, y) = x + y

sum3 : Nat * Nat * Nat -> Nat
sum3(a, b, c) = add_nat(add_nat(a, b), c)
";
    for (_fn_name, sig_results) in check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, CheckResult::Proved, "`{label}` should be Proved");
        }
    }
}

// ── Division safety ───────────────────────────────────────────────────────────

#[test]
fn division_by_literal_proved() {
    proved("
half : Int -> Int
half(x) = x / 2
");
}

#[test]
fn division_unconstrained_denominator_counterexample() {
    counterexample("
unsafe_div : Int * Int -> Int
unsafe_div(x, y) = x / y
");
}

#[test]
fn division_unconstrained_single_param_counterexample() {
    counterexample("
recip : Int -> Int
recip(x) = 1 / x
");
}

#[test]
fn division_by_zero_reason_in_result() {
    let results = check("
unsafe_div : Int * Int -> Int
unsafe_div(x, y) = x / y
");
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample");
    };
    assert_eq!(reason, "division by zero");
}

#[test]
fn range_violation_reason_in_result() {
    let results = check("
negate : Nat -> Nat
negate(x) = -x
");
    let (_, result) = results.into_iter().next().unwrap();
    let CheckResult::Counterexample { reason, .. } = result else {
        panic!("expected counterexample");
    };
    assert!(reason.contains("not in"), "reason should say 'not in …': {reason}");
    assert!(reason.contains("Nat"), "reason should name the range: {reason}");
}

#[test]
fn division_excluded_zero_domain_proved() {
    proved("
safe_recip : Int - {0} -> Int
safe_recip(x) = 1 / x
");
}

#[test]
fn division_two_arg_excluded_zero_proved() {
    proved("
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y
");
}

// ── Try operator (?) ──────────────────────────────────────────────────────────

#[test]
fn try_propagates_fail_proved() {
    proved_all("
safe_to_nat : Int -> Nat | Fail
safe_to_nat(x) {
    assert x in Nat
    x
}

caller : Int -> Nat | Fail
caller(n) {
    mut x: Nat = safe_to_nat(n)?
    x + 1
}
");
}

#[test]
fn try_in_expression_body_proved() {
    proved_all("
safe_to_nat : Int -> Nat | Fail
safe_to_nat(x) {
    assert x in Nat
    x
}

wrap : Int -> Nat | Fail
wrap(n) = safe_to_nat(n)?
");
}

#[test]
fn fail_set_in_membership_is_false() {
    counterexample("
bad : Int -> Nat | Fail
bad(x) = x
");
}

// ── Constants ─────────────────────────────────────────────────────────────────

#[test]
fn const_type_check_proved() {
    let results = check("pi : Nat\npi = 314");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, CheckResult::Proved);
}

#[test]
fn const_type_check_fails_wrong_type() {
    let results = check("neg : Nat\nneg = -1");
    assert_eq!(results.len(), 1);
    assert!(matches!(results[0].1, CheckResult::Counterexample { .. }));
}

#[test]
fn const_used_in_function_proved() {
    proved_all("
base : Nat
base = 10

add_base : Nat -> Nat
add_base(x) = x + base
");
}

#[test]
fn chained_constants_proved() {
    proved_all("
pi : Nat
pi = 314

tau : Nat
tau = 2 * pi
");
}

#[test]
fn const_literal_proved() {
    proved_all("
answer : Nat
answer = 42
");
}

#[test]
fn const_negative_not_nat() {
    let results = check("bad : Nat\nbad = -5");
    assert_eq!(results.len(), 1);
    assert!(matches!(results[0].1, CheckResult::Counterexample { .. }));
}
