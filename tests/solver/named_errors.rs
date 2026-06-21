use super::helpers::*;

// ── Named error sets in range annotations ─────────────────────────────────────

#[test]
fn named_error_set_in_range_proved() {
    proved("
HTTPError = {400, 503}
fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 400
");
}

#[test]
fn named_error_set_in_range_counterexample() {
    // Negative values are neither in Nat nor in {400, 503}.
    counterexample("
HTTPError = {400, 503}
fetch : Int -> Nat | HTTPError
fetch(x) = x
");
}

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

#[test]
fn named_error_set_with_fail_proved() {
    proved("
HTTPError = {400, 503}
fallible_fetch : Int -> Nat | HTTPError | Fail
fallible_fetch(x) {
    assert x >= 0
    if x > 0 then x else 400
}
");
}

#[test]
fn named_error_propagation_via_try_proved() {
    // After `?`, the value is in `Nat | HTTPError`. Since both 400 and 503 are
    // in Nat, the solver sees the result as in Nat and proves `Int` range.
    proved_all("
HTTPError = {400, 503}

fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 400

caller : Int -> Int
caller(x) {
    result : Int = fetch(x)?
    result
}
");
}

#[test]
fn named_error_set_two_callers_proved() {
    proved_all("
HTTPError = {400, 503}

fetch : Int -> Nat | HTTPError
fetch(x) = if x > 0 then x else 503

double_fetch : Int -> Nat | HTTPError
double_fetch(x) {
    a : Int = fetch(x)?
    b : Int = fetch(x)?
    a + b
}
");
}
