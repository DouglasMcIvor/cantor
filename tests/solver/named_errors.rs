use super::helpers::*;

// ── Named error sets used as sole range ───────────────────────────────────────

#[test]
fn named_error_set_as_sole_range_proved() {
    proved(
        "
HTTPError = {400, 503}
always_not_found : Int -> HTTPError
always_not_found(x) = 400
",
    );
}

#[test]
fn named_error_set_as_sole_range_counterexample() {
    counterexample(
        "
HTTPError = {400, 503}
bad_error : Int -> HTTPError
bad_error(x) = 200
",
    );
}

// ── `!!` (error-union) in the range annotation ────────────────────────────────

#[test]
fn bang_bang_range_proved() {
    // Success path (x > 0) returns x ∈ Nat; failure path returns a valid error
    // via `fail 400` (encoded as an offset value distinct from any Nat).
    proved(
        "
HTTPError = {400, 503}
fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400
",
    );
}

#[test]
fn bang_bang_success_path_counterexample() {
    // `x` can be negative or zero: not in Nat and not an error value.
    counterexample(
        "
HTTPError = {400, 503}
bad_fetch : Int -> Nat !! HTTPError
bad_fetch(x) = x
",
    );
}

#[test]
fn bang_bang_invalid_error_code_counterexample() {
    // Failure path returns `fail 200`, but 200 ∉ HTTPError = {400, 503}.
    counterexample(
        "
HTTPError = {400, 503}
bad_error_code : Int -> Nat !! HTTPError
bad_error_code(x) = if x > 0 then x else fail 200
",
    );
}

// ── `!!` with block body and assert ──────────────────────────────────────────

#[test]
fn bang_bang_assert_with_fail_clause_proved() {
    // `assert x > 0` cannot be proved statically for all Int inputs, so it
    // becomes a runtime check. The `else fail 400` clause returns a valid error.
    // Because the range includes `!!` (which counts as containing Fail), the
    // compiler accepts a runtime assert.  After the assert the solver knows x > 0,
    // so returning x proves the Nat part of the range.
    proved(
        "
HTTPError = {400, 503}
fallible_fetch : Int -> Nat !! HTTPError
fallible_fetch(x) {
    assert x > 0 else fail 400
    x
}
",
    );
}

// ── `?` (try) propagation with `!!` ──────────────────────────────────────────

#[test]
fn bang_bang_try_propagation_proved() {
    // After `fetch(x)?`, on the success path `result` is in Nat.
    // On the failure path `?` propagates the error to `caller`, which also
    // declares `Nat !! HTTPError` so it may return errors.
    // Expected: both functions proved.
    proved_all(
        "
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 400

caller : Int -> Nat !! HTTPError
caller(x) {
    result : Nat = fetch(x)?
    result
}
",
    );
}

#[test]
fn bang_bang_two_callers_proved() {
    // Two sequential `?` calls — if either fails the error propagates.
    // On the success path both `a` and `b` are in Nat, so `a + b` is in Nat.
    // Expected: both functions proved.
    proved_all(
        "
HTTPError = {400, 503}

fetch : Int -> Nat !! HTTPError
fetch(x) = if x > 0 then x else fail 503

double_fetch : Int -> Nat !! HTTPError
double_fetch(x) {
    a : Nat = fetch(x)?
    b : Nat = fetch(x)?
    a + b
}
",
    );
}

// ── `Fail` sentinel-collision and extraction correctness ─────────────────────
//
// `Fail` used to be encoded as a sentinel integer (`i64::MIN`, `i64::MIN+1+n`),
// which bypassed the cross-kind union datatype machinery for the common case
// and produced false proofs whenever the error payload's own set was
// unbounded (its "decode" predicate `t - (i64::MIN+1) ∈ B` holds for nearly
// every representable machine integer). `Fail` is now a builtin distinct
// sort, routed through the exact same datatype machinery as any other union
// arm — see docs/design-decisions.md §13.

#[test]
fn sentinel_collision_unbounded_payload_counterexample() {
    // Previously falsely `Proved`: under the old sentinel scheme, `Nat |
    // (Fail * Int)`'s membership check collapsed to `Unconstrained` because
    // the unbounded `Int` payload's decode predicate is satisfiable for
    // every representable value, discarding the `Nat` obligation entirely.
    // The body always returns `-1`, which is a genuine success value (no
    // `fail` in sight) and isn't in `Nat`.
    counterexample(
        "
buggy : Int -> Nat | (Fail * Int)
buggy(x) = -1
",
    );
}

#[test]
fn sentinel_collision_unbounded_payload_valid_success_proved() {
    // Same range as above, but the body is a genuine, valid success value —
    // confirms the fix doesn't just reject everything.
    proved(
        "
ok : Int -> Nat | (Fail * Int)
ok(x) = if x >= 0 then x else fail x
",
    );
}

#[test]
fn try_extraction_arithmetic_proved() {
    // `?` must narrow to the *success value itself* (Nat), not the whole
    // tagged `Nat | Fail` wrapper — otherwise `y - 1` would be arithmetic on
    // a non-integer-sorted term. The guard against `y == 0` is required for
    // this to actually be in range; a matching counterexample test below
    // confirms the guard is load-bearing, not just accepted regardless.
    proved_all(
        "
fetch : Int -> Nat | Fail
fetch(x) = if x > 0 then x else fail

caller : Int -> Nat | Fail
caller(x) {
    y : Nat = fetch(x)?
    if y == 0 then 0 else y - 1
}
",
    );
}

#[test]
fn try_extraction_arithmetic_unguarded_counterexample() {
    // Same as above but without the `y == 0` guard: `y - 1` is `-1` when
    // `y == 0`, which is out of `Nat`. If `?` extraction were broken (e.g.
    // silently degrading `y - 1` to a dummy value instead of doing real
    // arithmetic on the extracted success value), this would falsely prove.
    let results = check_all(
        "
fetch : Int -> Nat | Fail
fetch(x) = if x > 0 then x else fail

caller : Int -> Nat | Fail
caller(x) {
    y : Nat = fetch(x)?
    y - 1
}
",
    );
    assert!(
        matches!(
            result_for(&results, "caller"),
            CheckResult::Counterexample { .. }
        ),
        "expected counterexample for caller, got {:?}",
        result_for(&results, "caller")
    );
}
