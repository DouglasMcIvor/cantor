use super::helpers::*;

// ── `None` used as sole/union range ─────────────────────────────────────────

#[test]
fn none_as_union_arm_proved() {
    proved(
        "
lookup : Int -> Nat | None
lookup(x) = if x >= 0 then x else none
",
    );
}

#[test]
fn none_success_path_counterexample() {
    // `x` can be negative, and the else branch is `none` (not an out-of-range
    // Int) — the only way this can fail to prove is if the success arm isn't
    // actually enforced. Returning `x` unconditionally (never `none`) must
    // still satisfy `Nat | None` only when `x` is always in `Nat`, which it
    // isn't here (`x` ranges over all of `Int`).
    counterexample(
        "
bad_lookup : Int -> Nat | None
bad_lookup(x) = x
",
    );
}

// ── `?` (try) propagation with `None` ───────────────────────────────────────

#[test]
fn try_propagation_none_proved() {
    // After `lookup(x)?`, on the success path `result` is in Nat. On the
    // `none` path `?` propagates `none` to `caller`, which also declares
    // `Nat | None` so it may return `none`.
    proved_all(
        "
lookup : Int -> Nat | None
lookup(x) = if x >= 0 then x else none

caller : Int -> Nat | None
caller(x) {
    result : Nat = lookup(x)?
    result
}
",
    );
}

#[test]
fn try_extraction_arithmetic_none_proved() {
    // Mirrors `named_errors::try_extraction_arithmetic_proved` for `Fail`:
    // `?` must narrow to the success value itself (Nat), not the whole
    // tagged `Nat | None` wrapper.
    proved_all(
        "
lookup : Int -> Nat | None
lookup(x) = if x > 0 then x else none

caller : Int -> Nat | None
caller(x) {
    y : Nat = lookup(x)?
    if y == 0 then 0 else y - 1
}
",
    );
}

#[test]
fn try_none_without_none_in_own_range_counterexample() {
    // `caller`'s own range is plain `Nat` — it never declares `None` — so a
    // `?` on a callee that can return `none` must be rejected rather than
    // silently proved (which would otherwise crash codegen with an LLVM
    // return-type mismatch: the callee compiles to a `{tag, i64}` struct,
    // but `caller` is declared to return a bare i64).
    let results = check_all(
        "
lookup : Int -> Nat | None
lookup(x) = if x >= 0 then x else none

caller : Int -> Nat
caller(x) = lookup(x)? + 1
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

// ── Full coexistence: `T | Fail | None` ─────────────────────────────────────

#[test]
fn fail_and_none_coexist_proved() {
    proved(
        "
classify : Int -> Nat | Fail | None
classify(x) {
    assert x != 0
    if x > 0 then x else none
}
",
    );
}

#[test]
fn try_propagation_fail_and_none_proved() {
    proved_all(
        "
classify : Int -> Nat | Fail | None
classify(x) {
    assert x != 0
    if x > 0 then x else none
}

caller : Int -> Nat | Fail | None
caller(x) {
    y : Nat = classify(x)?
    y + 1
}
",
    );
}

#[test]
fn try_none_partial_range_counterexample() {
    // `caller` declares `Fail` but not `None`; `classify` can propagate
    // either. Missing just one of the two required tags must still be
    // rejected.
    let results = check_all(
        "
classify : Int -> Nat | Fail | None
classify(x) {
    assert x != 0
    if x > 0 then x else none
}

caller : Int -> Nat | Fail
caller(x) = classify(x)? + 1
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
