use cantor::{
    parser::parse_file,
    solver::{CheckResult, check_file},
};

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Parse `src`, build the full function environment, and return the results
/// for every function in the file.
fn check_all(src: &str) -> Vec<(String, Vec<(String, CheckResult)>)> {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    check_file(&items).unwrap_or_else(|e| panic!("check error: {e}"))
}

/// Parse a single-function source, check it, and return its signature results.
fn check(src: &str) -> Vec<(String, CheckResult)> {
    let mut all = check_all(src);
    assert_eq!(all.len(), 1, "expected exactly one function");
    all.remove(0).1
}

/// Assert that the first (usually only) signature of a single-function source is Proved.
fn proved(src: &str) {
    for (label, result) in &check(src) {
        assert_eq!(result, &CheckResult::Proved, "`{label}` should be Proved, got {result:?}");
    }
}

/// Assert that the single-function source produces at least one Counterexample.
fn counterexample(src: &str) {
    let results = check(src);
    let (label, result) = results.into_iter().next().unwrap();
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "expected Counterexample for `{label}`, got {result:?}"
    );
}

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

// ── IntN ranges ──────────────────────────────────────────────────────────────

#[test]
fn int16_identity_stays_int16() {
    proved("id16 : Int16 -> Int16\nid16(x) = x");
}

#[test]
fn int16_double_overflows() {
    counterexample("double16 : Int16 -> Int16\ndouble16(x) = x + x");
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
    // quad's proof uses double's Nat->Nat contract, not its body.
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
    // succ_nat : Nat -> NatPos — adds 1, so result > 0.
    // wrap_succ just delegates; the contract of succ_nat is enough to prove it.
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
    // negate : Nat -> Int  (legal — negation can be negative).
    // caller claims result is Nat, but -x is not always ≥ 0.
    let src = "
negate : Nat -> Int
negate(x) = -x

caller : Nat -> Nat
caller(x) = negate(x)
";
    let all = check_all(src);
    // `negate` itself is proved (Int is unconstrained).
    let negate_result = all.iter().find(|(n, _)| n == "negate").unwrap();
    assert_eq!(negate_result.1[0].1, CheckResult::Proved);
    // `caller` should get a counterexample — negate's contract only guarantees Int, not Nat.
    let caller_result = all.iter().find(|(n, _)| n == "caller").unwrap();
    assert!(
        matches!(caller_result.1[0].1, CheckResult::Counterexample { .. }),
        "caller should be Counterexample, got {:?}", caller_result.1[0].1
    );
}

#[test]
fn recursive_function_proved_via_own_contract() {
    // factorial : NatPos -> NatPos (we're just checking range, not termination).
    // The recursive call uses the function's own signature as the induction hypothesis.
    let src = "
factorial : NatPos -> NatPos
factorial(n) = if n == 1 then 1 else n * factorial(n - 1)
";
    // The own-signature contract says factorial(n-1) ∈ NatPos, so n * NatPos ∈ NatPos
    // when n ∈ NatPos. Should be Proved.
    proved(src);
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

// ── Set expressions in signatures ─────────────────────────────────────────────

#[test]
fn set_difference_domain_proved() {
    // Division is safe when the divisor is guaranteed non-zero.
    proved("
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y
");
}

#[test]
fn set_difference_single_arg_proved() {
    // A function from (Int - {0}) that always returns 1 or -1 stays in NatPos
    // only if we restrict to NatPos domain.
    proved("
sign : NatPos - {0} -> NatPos
sign(x) = 1
");
}

#[test]
fn singleton_set_range_proved() {
    // A constant function f(x) = 42 always lands in {42}.
    proved("
constant42 : Int -> {42}
constant42(x) = 42
");
}

#[test]
fn singleton_set_range_counterexample() {
    // f(x) = x does NOT always land in {42}.
    counterexample("
not_constant : Int -> {42}
not_constant(x) = x
");
}

#[test]
fn singleton_domain_proved() {
    // If the domain is {0}, the body x + 1 is always 1, which is in NatPos.
    proved("
succ_zero : {0} -> NatPos
succ_zero(x) = x + 1
");
}

#[test]
fn set_union_domain_proved() {
    // Int8 | Int16 is just Int16 (Int8 ⊆ Int16), but the checker only needs
    // to know that the output is in Int (trivially true range).
    proved("
widen : Int8 | Int16 -> Int
widen(x) = x
");
}

#[test]
fn set_intersection_domain_proved() {
    // Nat & Int16 = { 0..32767 }; x + 1 ≤ 32768, still in Int.
    proved("
narrow : Nat & Int16 -> Nat
narrow(x) = x
");
}

#[test]
fn multi_element_set_lit_range_proved() {
    proved("
bool_to_bit : Int -> {0, 1}
bool_to_bit(x) = if x == 0 then 0 else 1
");
}

#[test]
fn multi_element_set_lit_range_counterexample() {
    counterexample("
bad_bit : Int -> {0, 1}
bad_bit(x) = x + x
");
}

#[test]
fn safe_div_fixture_all_proved() {
    // Matches tests/cantor_files/safe_div.cantor.
    let src = "
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y

positive_div : NatPos * NatPos -> Nat
positive_div(x, y) = x / y
";
    for (_fn_name, sig_results) in check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, CheckResult::Proved, "`{label}` should be Proved");
        }
    }
}
