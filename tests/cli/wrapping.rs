//! `Signed32`/`Unsigned32` — wrapping fixed-width integers, end to end. See
//! docs/wrapping-and-quotient-sets-plan.md, Feature 1.

use super::helpers::*;

#[test]
fn signed32_add_wraps_at_i32_max() {
    // i32::MAX + 1 wraps to i32::MIN — the headline example.
    let out = run_subcommand("wrapping_signed32_add_overflow.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = -2147483648"),
        "expected i32::MAX + 1 == i32::MIN:\n{}",
        out.stdout
    );
}

#[test]
fn unsigned32_add_wraps_at_u32_max() {
    // u32::MAX + 1 wraps to 0.
    let out = run_subcommand("wrapping_unsigned32_add_overflow.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 0"),
        "expected u32::MAX + 1 == 0:\n{}",
        out.stdout
    );
}

#[test]
fn signed32_sub_wraps_at_i32_min() {
    // i32::MIN - 1 wraps to i32::MAX.
    let out = run_subcommand("wrapping_signed32_sub_overflow.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 2147483647"),
        "expected i32::MIN - 1 == i32::MAX:\n{}",
        out.stdout
    );
}

#[test]
fn signed32_mul_wraps() {
    // 2147483647 * 2 = 4294967294, which reads back as -2 in Signed32's
    // two's-complement bit pattern.
    let out = run_subcommand("wrapping_signed32_mul_overflow.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = -2"),
        "expected 2147483647 * 2 == -2 (mod 2^32, signed reading):\n{}",
        out.stdout
    );
}

#[test]
fn signed32_neg_min_wraps_to_itself() {
    // Negating i32::MIN wraps back to itself — no guard needed, unlike
    // Int's checked overflow-then-abort model at i64::MIN.
    let out = run_subcommand("wrapping_signed32_neg_min.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = -2147483648"),
        "expected -i32::MIN == i32::MIN:\n{}",
        out.stdout
    );
}

#[test]
fn signed_vs_unsigned_comparison_same_bits_different_meaning() {
    // The same all-ones bit pattern is -1 read as Signed32, but u32::MAX
    // read as Unsigned32 — a good gotcha for the docs appendix.
    let out = run_subcommand("wrapping_signed_unsigned_comparison.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected both comparisons to hold:\n{}",
        out.stdout
    );
}

#[test]
fn from_round_trips_both_signed_and_unsigned() {
    let out = run_subcommand("wrapping_from_roundtrip.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected from(signed32(100)) == 100 and from(unsigned32(100)) == 100:\n{}",
        out.stdout
    );
}

#[test]
fn int_into_signed32_domain_is_a_counterexample() {
    // Signed32 is fully disjoint from Int (fork 1) — a raw Int value is
    // never a member, exactly like passing a plain Int where a `distinct`
    // value is expected.
    let out = run_file("wrapping_int_into_signed32_domain_violation.cantor");
    assert_ne!(out.code, 0, "should refuse to run:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  bad"),
        "expected a counterexample for bad:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected a domain-violation reason:\n{}",
        out.stdout
    );
}

#[test]
fn signed32_into_unsigned32_domain_is_a_counterexample() {
    // Signed32/Unsigned32 are mutually disjoint too, not just each disjoint
    // from Int — each gets its own opaque solver sort, not a shared bit
    // pattern space.
    let out = run_file("wrapping_signed32_into_unsigned32_domain_violation.cantor");
    assert_ne!(out.code, 0, "should refuse to run:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  bad"),
        "expected a counterexample for bad:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected a domain-violation reason:\n{}",
        out.stdout
    );
}
