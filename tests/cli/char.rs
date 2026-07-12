//! `Char` — a Unicode scalar value, end to end. See docs/design-decisions.md §13.

use super::helpers::*;

#[test]
fn char_prints_as_the_actual_character() {
    let out = run_subcommand("char_ascii_construct.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = A"),
        "expected char(65) to print as 'A':\n{}",
        out.stdout
    );
}

#[test]
fn from_unwraps_char_to_its_codepoint() {
    let out = run_subcommand("char_from_roundtrip.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected from(char(97)) == 97:\n{}",
        out.stdout
    );
}

#[test]
fn surrogate_codepoint_is_a_counterexample() {
    // 0xD800 is a UTF-16 surrogate, not a valid Unicode scalar value —
    // char()'s basis obligation rejects it at compile time, same graduated
    // treatment as `/`'s NonZeroInt check.
    let out = run_file("char_surrogate_domain_violation.cantor");
    assert_ne!(out.code, 0, "should refuse to run:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  main"),
        "expected a counterexample for main:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("must be a valid Unicode scalar value"),
        "expected the basis-obligation reason:\n{}",
        out.stdout
    );
}

#[test]
fn int_into_char_domain_is_a_counterexample() {
    // Char is fully disjoint from Int — a raw Int value is never a member,
    // exactly like Signed32/Unsigned32's disjointness from Int.
    let out = run_file("char_int_domain_violation.cantor");
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

// ── `Char*` (strings) ──────────────────────────────────────────────────────────

#[test]
fn char_star_prints_as_text() {
    let out = run_subcommand("char_string_construct.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = Hello"),
        "expected the Char* to print as text, not codepoints:\n{}",
        out.stdout
    );
}

#[test]
fn char_star_indexing_returns_truncated_char() {
    let out = run_subcommand("char_string_index.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = e"),
        "expected \"Hello\"[1] == 'e':\n{}",
        out.stdout
    );
}

#[test]
fn char_star_concat() {
    let out = run_subcommand("char_string_concat.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = Hi!"),
        "expected \"Hi\" ++ \"!\" == \"Hi!\":\n{}",
        out.stdout
    );
}
