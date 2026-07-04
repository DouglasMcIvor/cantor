use cantor::runtime::{
    CantorBoolSet, CantorIntSet, cantor_bigint_add, cantor_bigint_cmp, cantor_bigint_div,
    cantor_bigint_from_i64, cantor_bigint_mul, cantor_bigint_neg, cantor_bigint_sub,
    cantor_bigint_to_i64, cantor_bigint_to_string,
};

// ── CantorIntSet ──────────────────────────────────────────────────────────────

#[test]
fn int_set_empty() {
    let s = CantorIntSet::default();
    assert_eq!(s.size(), 0);
    assert!(!s.contains(0));
}

#[test]
fn int_set_insert_and_contains() {
    let mut s = CantorIntSet::default();
    s.insert(3);
    s.insert(1);
    s.insert(2);
    assert!(s.contains(1));
    assert!(s.contains(2));
    assert!(s.contains(3));
    assert!(!s.contains(0));
    assert!(!s.contains(4));
}

#[test]
fn int_set_deduplicates() {
    let mut s = CantorIntSet::default();
    s.insert(5);
    s.insert(5);
    s.insert(5);
    assert_eq!(s.size(), 1);
}

#[test]
fn int_set_sorted_iteration_order() {
    let mut s = CantorIntSet::default();
    for v in [3, 1, 4, 1, 5, 9, 2, 6] {
        s.insert(v);
    }
    let got: Vec<i64> = (0..s.size()).map(|i| s.get(i)).collect();
    assert_eq!(got, vec![1, 2, 3, 4, 5, 6, 9]);
}

#[test]
fn int_set_negatives_and_zero() {
    let mut s = CantorIntSet::default();
    for v in [0, -1, -3, 2, -2, 1] {
        s.insert(v);
    }
    let got: Vec<i64> = (0..s.size()).map(|i| s.get(i)).collect();
    assert_eq!(got, vec![-3, -2, -1, 0, 1, 2]);
}

// ── CantorBoolSet ─────────────────────────────────────────────────────────────

#[test]
fn bool_set_empty() {
    let s = CantorBoolSet::default();
    assert_eq!(s.size(), 0);
    assert!(!s.contains(false));
    assert!(!s.contains(true));
}

#[test]
fn bool_set_insert_false_only() {
    let mut s = CantorBoolSet::default();
    s.insert(false);
    assert_eq!(s.size(), 1);
    assert!(s.contains(false));
    assert!(!s.contains(true));
    assert_eq!(s.get(0), 0);
}

#[test]
fn bool_set_insert_true_only() {
    let mut s = CantorBoolSet::default();
    s.insert(true);
    assert_eq!(s.size(), 1);
    assert!(!s.contains(false));
    assert!(s.contains(true));
    assert_eq!(s.get(0), 1);
}

#[test]
fn bool_set_both_values_sorted() {
    let mut s = CantorBoolSet::default();
    s.insert(true);
    s.insert(false);
    assert_eq!(s.size(), 2);
    // false (0) sorts before true (1)
    assert_eq!(s.get(0), 0);
    assert_eq!(s.get(1), 1);
}

#[test]
fn bool_set_deduplicates() {
    let mut s = CantorBoolSet::default();
    s.insert(true);
    s.insert(true);
    s.insert(false);
    s.insert(false);
    assert_eq!(s.size(), 2);
}

// ── CantorBigInt (int-soundness-plan phase 3, step 1: runtime only) ──────────
//
// All `cantor_bigint_*` entry points take/return tagged words (see the
// module doc comment in `src/runtime/mod.rs`); these tests only ever go
// through that public, tag-aware API — never the private encode/decode
// helpers — since that's the actual contract codegen will rely on later.

fn to_string(word: i64) -> String {
    let ptr = cantor_bigint_to_string(word) as *const std::ffi::c_char;
    unsafe { std::ffi::CStr::from_ptr(ptr) }
        .to_string_lossy()
        .into_owned()
}

#[test]
fn from_i64_round_trips_through_to_string() {
    for n in [0i64, 1, -1, 42, -42, i64::MAX, i64::MIN] {
        assert_eq!(to_string(cantor_bigint_from_i64(n)), n.to_string());
    }
}

#[test]
fn add_small_stays_exact() {
    let sum = cantor_bigint_add(cantor_bigint_from_i64(2), cantor_bigint_from_i64(3));
    assert_eq!(to_string(sum), "5");
}

#[test]
fn add_overflows_i64_and_promotes() {
    let sum = cantor_bigint_add(cantor_bigint_from_i64(i64::MAX), cantor_bigint_from_i64(1));
    let expected = (i64::MAX as i128) + 1;
    assert_eq!(to_string(sum), expected.to_string());
}

#[test]
fn sub_underflows_i64_and_promotes() {
    let diff = cantor_bigint_sub(cantor_bigint_from_i64(i64::MIN), cantor_bigint_from_i64(1));
    let expected = (i64::MIN as i128) - 1;
    assert_eq!(to_string(diff), expected.to_string());
}

#[test]
fn mul_small_stays_exact() {
    let product = cantor_bigint_mul(cantor_bigint_from_i64(6), cantor_bigint_from_i64(7));
    assert_eq!(to_string(product), "42");
}

#[test]
fn mul_overflows_i64_and_promotes() {
    let product = cantor_bigint_mul(cantor_bigint_from_i64(i64::MAX), cantor_bigint_from_i64(2));
    let expected = (i64::MAX as i128) * 2;
    assert_eq!(to_string(product), expected.to_string());
}

#[test]
fn mul_of_two_maxima_stays_correct_beyond_i128_boundary_case() {
    // (i64::MAX)^2 comfortably exceeds i64 but still fits i128 — the fast
    // small/small path's own overflow-detection boundary.
    let product = cantor_bigint_mul(
        cantor_bigint_from_i64(i64::MAX),
        cantor_bigint_from_i64(i64::MAX),
    );
    let expected = (i64::MAX as i128) * (i64::MAX as i128);
    assert_eq!(to_string(product), expected.to_string());
}

#[test]
fn div_truncates_toward_zero_not_floor() {
    // -7 / 2 truncates to -3 (not floor's -4) — Cantor's declared `/` semantics.
    let q = cantor_bigint_div(cantor_bigint_from_i64(-7), cantor_bigint_from_i64(2));
    assert_eq!(to_string(q), "-3");
    let q = cantor_bigint_div(cantor_bigint_from_i64(7), cantor_bigint_from_i64(-2));
    assert_eq!(to_string(q), "-3");
    let q = cantor_bigint_div(cantor_bigint_from_i64(7), cantor_bigint_from_i64(2));
    assert_eq!(to_string(q), "3");
}

#[test]
fn neg_small_value() {
    assert_eq!(
        to_string(cantor_bigint_neg(cantor_bigint_from_i64(5))),
        "-5"
    );
    assert_eq!(
        to_string(cantor_bigint_neg(cantor_bigint_from_i64(-5))),
        "5"
    );
    assert_eq!(to_string(cantor_bigint_neg(cantor_bigint_from_i64(0))), "0");
}

#[test]
fn neg_promotes_at_the_tagged_schemes_own_boundary() {
    // 2^62 fits in a plain i64 (well within Int64) but not in the tagged
    // scheme's narrower small-int range, so its negation must box — the
    // wrinkle documented in int-soundness-plan.md's "Phase 3" section.
    let n: i64 = 1 << 62;
    let negated = cantor_bigint_neg(cantor_bigint_from_i64(-n));
    assert_eq!(to_string(negated), n.to_string());
}

#[test]
fn cmp_orders_small_values() {
    let a = cantor_bigint_from_i64(1);
    let b = cantor_bigint_from_i64(2);
    assert_eq!(cantor_bigint_cmp(a, b), -1);
    assert_eq!(cantor_bigint_cmp(b, a), 1);
    assert_eq!(cantor_bigint_cmp(a, a), 0);
}

#[test]
fn cmp_orders_boxed_values_and_mixed_small_and_boxed() {
    let small = cantor_bigint_from_i64(1);
    let big = cantor_bigint_mul(
        cantor_bigint_from_i64(i64::MAX),
        cantor_bigint_from_i64(i64::MAX),
    );
    assert_eq!(cantor_bigint_cmp(small, big), -1);
    assert_eq!(cantor_bigint_cmp(big, small), 1);
    assert_eq!(cantor_bigint_cmp(big, big), 0);
}

#[test]
fn to_i64_round_trips_through_from_i64_for_small_and_boxed_values() {
    for n in [0i64, 1, -1, 42, -42, i64::MAX, i64::MIN, 1 << 62, -(1 << 62)] {
        assert_eq!(cantor_bigint_to_i64(cantor_bigint_from_i64(n)), n);
    }
}

// `cantor_bigint_to_i64` aborts the process (does not panic — see its own
// doc comment) if the boxed value genuinely doesn't fit in i64, violating
// the "already proved to fit" contract. Not exercised here: like
// `cantor_overflow_abort`/`cantor_dispatch_unreachable` elsewhere in this
// file, an abort path isn't safely testable from an ordinary in-process
// unit test (it would kill the whole test binary).
