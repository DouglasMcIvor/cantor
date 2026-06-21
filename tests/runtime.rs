use cantor::runtime::{CantorBoolSet, CantorIntSet};

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
