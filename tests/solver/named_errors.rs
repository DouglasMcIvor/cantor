use super::helpers::*;

// ── Named error sets used as sole range ───────────────────────────────────────

#[test]
fn named_error_set_as_sole_range_proved() {
    proved("
HTTPError = {400, 503}
always_not_found : Int -> HTTPError
always_not_found(x) = 400
");
}

#[test]
fn named_error_set_as_sole_range_counterexample() {
    counterexample("
HTTPError = {400, 503}
bad_error : Int -> HTTPError
bad_error(x) = 200
");
}

// ── `!!` (error-union) in the range annotation ────────────────────────────────

#[test]
fn bang_bang_range_proved() {
    // Success path (x > 0) returns x ∈ Nat; failure path returns a valid error
    // via `fail 400` (encoded as an offset value distinct from any Nat).
    proved("
HTTPError = {400, 503}
fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400
");
}

#[test]
fn bang_bang_success_path_counterexample() {
    // `x` can be negative or zero: not in Nat and not an error value.
    // Expected: counterexample.
    // NOTE: currently proves because `!!` ranges are Unconstrained in the solver.
    counterexample("
HTTPError = {400, 503}
bad_fetch : Int -> Nat !! HTTPError
bad_fetch(x) = x
");
}

#[test]
fn bang_bang_invalid_error_code_counterexample() {
    // Failure path returns `fail 200`, but 200 ∉ HTTPError = {400, 503}.
    // Expected: counterexample.
    // NOTE: currently proves because `!!` ranges are Unconstrained in the solver.
    counterexample("
HTTPError = {400, 503}
bad_error_code : Int -> Nat !! HTTPError
bad_error_code(x) = if x > 0 then x else fail 200
");
}

// ── `!!` with block body and assert ──────────────────────────────────────────

#[test]
fn bang_bang_assert_with_fail_clause_proved() {
    // `assert x > 0` cannot be proved statically for all Int inputs, so it
    // becomes a runtime check. The `else fail 400` clause returns a valid error.
    // Because the range includes `!!` (which counts as containing Fail), the
    // compiler accepts a runtime assert.  After the assert the solver knows x > 0,
    // so returning x proves the Nat part of the range.
    proved("
HTTPError = {400, 503}
fallible_fetch : Int -> Nat !! HTTPError
fallible_fetch(x) {
    assert x > 0 else fail 400
    x
}
");
}

// ── `?` (try) propagation with `!!` ──────────────────────────────────────────

#[test]
fn bang_bang_try_propagation_proved() {
    // After `fetch(x)?`, on the success path `result` is in Nat.
    // On the failure path `?` propagates the error to `caller`, which also
    // declares `Nat !! HTTPError` so it may return errors.
    // Expected: both functions proved.
    // NOTE: `result : Nat` currently counterexamples because the solver does not
    // yet extract the success-range from a `!!` callee contract.
    proved_all("
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

caller : Int -> Nat !! HTTPError
caller(x) {
    result : Nat = fetch(x)?
    result
}
");
}

#[test]
fn bang_bang_two_callers_proved() {
    // Two sequential `?` calls — if either fails the error propagates.
    // On the success path both `a` and `b` are in Nat, so `a + b` is in Nat.
    // Expected: both functions proved.
    // NOTE: same limitation as bang_bang_try_propagation_proved.
    proved_all("
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 503

double_fetch : Int -> Nat !! HTTPError
double_fetch(x) {
    a : Nat = fetch(x)?
    b : Nat = fetch(x)?
    a + b
}
");
}
