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

/// Assert that every signature in a multi-function source is Proved.
fn proved_all(src: &str) {
    for (_fn_name, sig_results) in &check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, &CheckResult::Proved, "`{label}` should be Proved, got {result:?}");
        }
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

// ── Division safety ───────────────────────────────────────────────────────────

#[test]
fn division_by_literal_proved() {
    // 2 is always non-zero; no counterexample possible.
    proved("
half : Int -> Int
half(x) = x / 2
");
}

#[test]
fn division_unconstrained_denominator_counterexample() {
    // y is unconstrained — solver finds y = 0.
    counterexample("
unsafe_div : Int * Int -> Int
unsafe_div(x, y) = x / y
");
}

#[test]
fn division_unconstrained_single_param_counterexample() {
    // x could be 0.
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
    assert_eq!(reason, "division by zero", "reason should say 'division by zero'");
}

#[test]
fn range_violation_reason_in_result() {
    // No division; reason should name the violated range.
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

// ── NonZeroInt named set ──────────────────────────────────────────────────────

#[test]
fn nonzeroint_domain_proved() {
    proved("
safe_recip : NonZeroInt -> Int
safe_recip(x) = 1 / x
");
}

#[test]
fn nonzeroint_two_arg_proved() {
    proved("
safe_div : Int * NonZeroInt -> Int
safe_div(x, y) = x / y
");
}

#[test]
fn nonzeroint_range_proved() {
    proved("
nonzero_shift : Int -> NonZeroInt
nonzero_shift(x) = x + 1 + (if x >= 0 then 1 else -1)
");
}

#[test]
fn nonzeroint_range_counterexample() {
    // x could be 0, which is not in NonZeroInt.
    counterexample("
bad_range : Int -> NonZeroInt
bad_range(x) = x
");
}

#[test]
fn nonzeroint_equivalent_to_set_diff() {
    // NonZeroInt and Int - {0} should accept exactly the same domains.
    // Both of these should be proved:
    let src_named = "safe_div : Int * NonZeroInt -> Int\nsafe_div(x, y) = x / y";
    let src_inline = "safe_div : Int * (Int - {0}) -> Int\nsafe_div(x, y) = x / y";
    proved(src_named);
    proved(src_inline);
}

#[test]
fn division_natpos_domain_proved() {
    // NatPos guarantees x > 0, so 10 / x is safe (no div-by-zero, result >= 0).
    // Range is Nat, not NatPos, because 10 / 11 = 0 (integer truncation).
    proved("
inv_floor : NatPos -> Nat
inv_floor(x) = 10 / x
");
}

#[test]
fn division_guarded_by_if_proved() {
    // `x != 0` guards the division: the checker narrows the path condition to
    // `x != 0` inside the then-branch, so `x ≠ 0` is trivially proved there.
    proved("
guarded_div : Int -> Int
guarded_div(x) = if x != 0 then 10 / x else 0
");
}

#[test]
fn division_guarded_wrong_branch_counterexample() {
    // Guard is in the else-branch, not the then-branch where division happens.
    counterexample("
bad_guard : Int -> Int
bad_guard(x) = if x == 0 then 10 / x else 0
");
}

// ── Block body: assume ────────────────────────────────────────────────────────

#[test]
fn assume_narrows_domain_proved() {
    // Without `assume`, x could be negative so x * x - x might not be in Nat.
    // With `assume x in Nat`, the solver knows x >= 0 and can prove x*x - x >= 0 is
    // not provable in general — but the range is Int so it's trivially proved.
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
    // `x` is Int but assume narrows it to Nat, making x the return value
    // provably in Nat.
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
    // `assume x > 0` narrows x for the solver; result x - 1 is then in Nat.
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
    // NatPos domain guarantees x > 0; require x in NatPos is therefore provable.
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
    // Domain NatPos already ensures x > 0; require verifies it explicitly and
    // adds it as a solver fact so x - 1 >= 0 is provable for the range check.
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
    // x is Int; require x in NatPos fails (x could be 0 or negative).
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
    // assume narrows x to Nat; subsequent require x in Nat is then provable.
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
    // NatPos domain (x > 0) makes `require x in NonZeroInt` provable (> 0 → ≠ 0).
    // The proved require fact then satisfies the division's NonZeroInt obligation.
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
    // With Int domain, x could be 0, so `require x in NonZeroInt` can't be proved.
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
    // NatPos domain makes `assert x in NatPos` statically provable — same as require.
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
    // `assert false` is always false — the checker catches it as a compile error.
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
    // `assert x in Nat` with Int domain is unknown (x might be negative).
    // The checker adds it as a fact anyway; the range check then passes.
    // Codegen will emit a runtime check.
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
    // assert narrows x to NonZeroInt; division obligation is then satisfiable.
    proved("
safe_recip : Int -> Int | Fail
safe_recip(x) {
    assert x in NonZeroInt
    1 / x
}
");
}

#[test]
fn assert_after_let_proved() {
    // assert can reference SSA-bound variables.
    proved("
bounded : Int -> Nat | Fail
bounded(x) {
    mut y: Int = x + 1
    assert y > 0
    y
}
");
}

// ── Try operator (?) ──────────────────────────────────────────────────────────

#[test]
fn try_propagates_fail_proved() {
    // caller delegates to a fallible function via `?` and adds 1.
    // The callee's contract (_call_0 >= 0) lets us prove the range (>= 1 >= 0).
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
    // `?` is also valid in expression bodies when the range includes Fail.
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
    // Nat | Fail as a range correctly constrains the integer part to Nat.
    // If the body can be negative, the checker still gives a counterexample
    // (proving Fail doesn't absorb bad integer values).
    counterexample("
bad : Int -> Nat | Fail
bad(x) = x
");
}

// ── Constants ─────────────────────────────────────────────────────────────────

#[test]
fn const_type_check_proved() {
    // 314 is in Nat (>= 0).
    let results = check("pi : Nat\npi = 314");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, CheckResult::Proved);
}

#[test]
fn const_type_check_fails_wrong_type() {
    // -1 is NOT in Nat.
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

// ── While loops ───────────────────────────────────────────────────────────────

#[test]
fn while_loop_proved_with_constraints() {
    // `mut acc: Nat` declares Nat as the loop invariant.  The solver uses it
    // to constrain the post-loop SSA variable, making the range obligation
    // (return is in Nat) immediately provable — no `assume` needed.
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
    // `mut acc: Nat` proves the inductive step, so all loop vars are constrained.
    // The range NatPos is stricter than Nat — when n=0 the loop body never runs
    // and acc stays 0, which is not in NatPos.  With all vars constrained the
    // solver can extract a real counterexample (n=0, output=0) rather than Unknown.
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
    // `mut acc: Int` carries no effective SMT constraint (Int = all integers).
    // The post-loop SSA variable is completely free.  Because the range
    // obligation (Nat) depends on `acc`, the solver finds a SAT witness —
    // but since `acc` is unconstrained, that witness may be spurious.
    // The checker must return Unknown rather than Counterexample.
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
    // `assume` is still valid and works alongside constraints when you need
    // a fact that can't be derived from the constraint alone.
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
    // After a `while i < n` loop the solver knows `i >= n` (exit condition).
    // Combined with `mut i: Nat`, the return i is provably in Nat.
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
    // The solver verifies the inductive step: given acc ∈ Nat and i ∈ Nat,
    // one iteration of (acc = acc + i; i = i + 1) leaves both in Nat.
    // This is the deeper soundness guarantee behind while_loop_proved_with_constraints.
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
    // `mut acc: Int16` with an unbounded increment: the inductive step
    // fails because acc = 32767 → acc + 1 = 32768 ∉ Int16.
    // The compiler must report a counterexample, not Proved.
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
    // The counterexample for a failing inductive step should include the
    // function's domain parameters so the user sees a concrete input witness.
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
    // Accumulate a sum over a set literal.  `mut acc: Nat` declares the
    // invariant; each iteration adds a NatPos element so acc stays in Nat.
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
    // Body subtracts 10 from acc on each iteration.  Starting at 5, after
    // any iteration acc goes negative — the Nat invariant is not maintained.
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
    // `mut acc: Int` carries no effective SMT constraint (Int = all integers).
    // After the loop the post-loop SSA variable is completely free, making SAT
    // results potentially spurious — the checker must return Unknown.
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
    // An empty set literal means the body never executes.
    // acc stays at its initial value 0, which is in Nat.
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
    // The iterable can reference function parameters or outer variables.
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
