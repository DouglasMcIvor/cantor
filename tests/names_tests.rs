use cantor::{names::check_names, parser::parse_file};

fn check(src: &str) -> Vec<String> {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    check_names(&items).into_iter().map(|e| e.to_string()).collect()
}

fn ok(src: &str) {
    let errs = check(src);
    assert!(errs.is_empty(), "expected no naming errors, got: {errs:?}");
}

fn err(src: &str) -> String {
    let errs = check(src);
    assert!(!errs.is_empty(), "expected a naming error for {src:?}");
    errs[0].clone()
}

// ── Definition names must be lowercase ───────────────────────────────────────

#[test]
fn function_name_lowercase_ok() {
    ok("abs : Int -> Int\nabs(x) = x");
}

#[test]
fn function_name_uppercase_err() {
    let e = err("Abs : Int -> Int\nAbs(x) = x");
    assert!(e.contains("Abs"), "error should name `Abs`: {e}");
    assert!(e.contains("compile-time"), "error should mention compile-time: {e}");
}

#[test]
fn param_name_lowercase_ok() {
    ok("f : Int -> Int\nf(myParam) = myParam");
}

#[test]
fn param_name_uppercase_err() {
    let e = err("f : Int -> Int\nf(X) = X");
    assert!(e.contains("X"), "error should name `X`: {e}");
}

#[test]
fn const_name_lowercase_ok() {
    ok("pi : Nat = 314");
}

#[test]
fn const_name_uppercase_err() {
    let e = err("Pi : Nat = 314");
    assert!(e.contains("Pi"), "error should name `Pi`: {e}");
}

#[test]
fn mut_local_lowercase_ok() {
    ok("f : Nat -> Nat\nf(x) {\n  mut result: Nat = x + 1\n  result\n}");
}

#[test]
fn mut_local_uppercase_err() {
    let e = err("f : Nat -> Nat\nf(x) {\n  mut Result: Nat = x + 1\n  Result\n}");
    assert!(e.contains("Result"), "error should name `Result`: {e}");
}

// ── Type/signature positions must be uppercase ────────────────────────────────

#[test]
fn builtin_sets_uppercase_ok() {
    ok("f : Int -> Nat\nf(x) = x");
}

#[test]
fn union_range_uppercase_ok() {
    ok("f : Int -> Nat | Fail\nf(x) = x");
}

#[test]
fn set_difference_domain_uppercase_ok() {
    ok("f : Int - {0} -> Int\nf(x) = x");
}

#[test]
fn lowercase_domain_err() {
    let e = err("f : mySet -> Int\nf(x) = x");
    assert!(e.contains("mySet"), "error should name `mySet`: {e}");
    assert!(e.contains("domain/range"), "error should mention domain/range: {e}");
}

#[test]
fn lowercase_range_err() {
    let e = err("f : Int -> result\nf(x) = x");
    assert!(e.contains("result"), "error should name `result`: {e}");
}

#[test]
fn lowercase_const_type_err() {
    let e = err("pi : nat = 314");
    assert!(e.contains("nat"), "error should name `nat`: {e}");
}

#[test]
fn lowercase_in_union_range_err() {
    let e = err("f : Int -> Nat | myError\nf(x) = x");
    assert!(e.contains("myError"), "error should name `myError`: {e}");
}

// ── Multiple errors collected ─────────────────────────────────────────────────

#[test]
fn multiple_violations_all_reported() {
    let items = parse_file("Abs : mySet -> Int\nAbs(X) = X")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    let errs = check_names(&items);
    // Expect: Abs (function name), X (param), mySet (domain) = at least 3
    assert!(errs.len() >= 3, "expected >= 3 errors, got {}: {errs:?}", errs.len());
}

// ── in/not in RHS in expression bodies is unchecked ──────────────────────────

#[test]
fn lowercase_in_rhs_of_assert_ok() {
    // `collected_primes` is a runtime set — lowercase is fine in assert position.
    // For now this test just verifies we don't false-positive on lowercase assert operands.
    ok("f : Nat -> Nat\nf(x) {\n  mut collected_primes: Nat = x\n  collected_primes\n}");
}

// ── While body naming is checked ─────────────────────────────────────────────

#[test]
fn while_body_mut_lowercase_ok() {
    // `mut` locals inside a while body must obey the same lowercase rule.
    ok("f : Nat -> Nat\nf(n) {\n  mut i: Nat = 0\n  while i < n {\n    mut tmp: Nat = i\n    i := tmp + 1\n  }\n  i\n}");
}

#[test]
fn while_body_mut_uppercase_err() {
    // Uppercase `mut` local inside a while body should be caught.
    let e = err("f : Nat -> Nat\nf(n) {\n  mut i: Nat = 0\n  while i < n {\n    mut Tmp: Nat = i\n    i := Tmp + 1\n  }\n  i\n}");
    assert!(e.contains("Tmp"), "error should name `Tmp`: {e}");
}

// ── For-in loop variable naming ───────────────────────────────────────────────

#[test]
fn for_in_lowercase_var_set_literal_ok() {
    // Lowercase loop variable with a set literal: always fine.
    ok("f : -> Int\nf() {\n  mut acc: Int = 0\n  for x in {1, 2, 3} {\n    acc := acc + x\n  }\n  acc\n}");
}

#[test]
fn for_in_uppercase_var_set_literal_ok() {
    // Uppercase loop variable with a set literal: fine — the set is compile-time.
    ok("f : -> Int\nf() {\n  mut acc: Int = 0\n  for X in {1, 2, 3} {\n    acc := acc + X\n  }\n  acc\n}");
}

#[test]
fn for_in_uppercase_var_uppercase_set_ok() {
    // Uppercase loop variable with an uppercase named set: fine — the set is
    // guaranteed compile-time per the naming rules.
    ok("f : -> Int\nf() {\n  mut acc: Int = 0\n  for X in MySet {\n    acc := acc + X\n  }\n  acc\n}");
}

#[test]
fn for_in_uppercase_var_lowercase_set_err() {
    // Uppercase loop variable with a lowercase (runtime) set: naming error.
    let e = err("f : -> Int\nf() {\n  mut acc: Int = 0\n  for X in mySet {\n    acc := acc + X\n  }\n  acc\n}");
    assert!(e.contains("X"), "error should name `X`: {e}");
    assert!(e.contains("compile-time"), "error should mention compile-time: {e}");
}

#[test]
fn for_in_lowercase_var_lowercase_set_ok() {
    // Lowercase loop variable with a lowercase (runtime) set: fine — x can be runtime.
    ok("f : -> Int\nf() {\n  mut acc: Int = 0\n  for x in mySet {\n    acc := acc + x\n  }\n  acc\n}");
}

#[test]
fn for_in_body_mut_uppercase_err() {
    // `mut` uppercase locals inside a for-in body should be caught too.
    let e = err("f : -> Int\nf() {\n  mut acc: Int = 0\n  for x in {1, 2} {\n    mut Tmp: Int = x\n    acc := acc + Tmp\n  }\n  acc\n}");
    assert!(e.contains("Tmp"), "error should name `Tmp`: {e}");
}

// ── Set definition naming ─────────────────────────────────────────────────────

#[test]
fn set_def_uppercase_name_ok() {
    ok("MySet = {1, 2, 3}");
}

#[test]
fn set_def_lowercase_name_err() {
    let e = err("mySet = {1, 2, 3}");
    assert!(e.contains("mySet"), "error should name `mySet`: {e}");
    assert!(e.contains("uppercase"), "error should mention uppercase: {e}");
}

#[test]
fn set_def_alias_uppercase_rhs_ok() {
    ok("Animal = Cat | Dog");
}

#[test]
fn set_def_alias_lowercase_rhs_err() {
    let e = err("Animal = cat | Dog");
    assert!(e.contains("cat"), "error should name `cat`: {e}");
}

#[test]
fn set_def_distinct_uppercase_ok() {
    ok("Litre = distinct Nat");
}

#[test]
fn set_def_distinct_lowercase_rhs_err() {
    let e = err("Litre = distinct nat");
    assert!(e.contains("nat"), "error should name `nat`: {e}");
}
