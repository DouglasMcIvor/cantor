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

// ── `'c'`/`"cat"` literal syntax ─────────────────────────────────────────────

#[test]
fn char_literal_prints_as_the_actual_character() {
    let out = run_subcommand("char_literal_construct.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = A"),
        "expected 'A' to print as 'A':\n{}",
        out.stdout
    );
}

#[test]
fn char_literal_from_roundtrip() {
    let out = run_subcommand("char_literal_from_roundtrip.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected from('a') == 97:\n{}",
        out.stdout
    );
}

#[test]
fn char_literal_ascii_escapes() {
    let out = run_subcommand("char_literal_escape.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected '\\n'/'\\t' to decode to 10/9:\n{}",
        out.stdout
    );
}

#[test]
fn char_literal_unicode_escape() {
    let out = run_subcommand("char_literal_unicode_escape.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected '\\u{{1F600}}' to decode to 128512:\n{}",
        out.stdout
    );
}

#[test]
fn char_literal_as_function_arg_widens_across_call_boundary() {
    // Regression test: passing a Char value as an argument to a
    // user-defined function needs the caller to widen the i32 register up
    // to the uniform i64 ABI slot — previously only builtins (`char`/`from`)
    // ever crossed this boundary, so no code path actually did this.
    let out = run_subcommand("char_literal_as_function_arg.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 65"),
        "expected codepoint('A') == 65:\n{}",
        out.stdout
    );
}

#[test]
fn char_literal_empty_is_a_parse_error() {
    let out = run_file("char_literal_empty.cantor");
    assert_ne!(out.code, 0, "should refuse to parse:\n{}", out.stdout);
    assert!(
        out.stderr.contains("empty char literal"),
        "expected an empty-char-literal diagnostic on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn char_literal_multi_char_is_a_parse_error() {
    let out = run_file("char_literal_multi.cantor");
    assert_ne!(out.code, 0, "should refuse to parse:\n{}", out.stdout);
    assert!(
        out.stderr.contains("exactly one character"),
        "expected a multi-char diagnostic on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn string_literal_prints_as_text() {
    let out = run_subcommand("string_literal_construct.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = Hello"),
        "expected \"Hello\" to print as text:\n{}",
        out.stdout
    );
}

#[test]
fn string_literal_empty_has_length_zero() {
    let out = run_subcommand("string_literal_empty.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 0"),
        "expected len(\"\") == 0:\n{}",
        out.stdout
    );
}

#[test]
fn string_literal_indexing() {
    let out = run_subcommand("string_literal_index.cantor");
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

// ── Char literals in set-expression position (`{'a', 'b'}` as a domain) ────

#[test]
fn char_set_literal_as_domain_proved() {
    let out = run_subcommand("char_set_lit_domain.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = a"),
        "expected f('a') == 'a' under domain {{'a', 'b'}}:\n{}",
        out.stdout
    );
}

#[test]
fn char_set_literal_domain_violation_is_a_counterexample() {
    let out = run_file("char_set_lit_domain_violation.cantor");
    assert_ne!(out.code, 0, "should refuse to run:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  main"),
        "expected a counterexample for main:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected a domain-violation reason:\n{}",
        out.stdout
    );
}

#[test]
fn char_set_literal_in_expression() {
    let out = run_subcommand("char_set_lit_membership.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 1"),
        "expected 'a' in {{'a', 'b'}} to be true:\n{}",
        out.stdout
    );
}

#[test]
fn char_set_literal_in_difference_domain_proved() {
    // Regression test for a completeness bug found during development: see
    // the fixture's own comment for the full story.
    let out = run_subcommand("char_set_lit_difference_domain.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = b"),
        "expected f('b') == 'b' under domain Char - {{'a'}}:\n{}",
        out.stdout
    );
}

#[test]
fn char_set_literal_in_difference_domain_violation_is_a_counterexample() {
    let out = run_file("char_set_lit_difference_domain_violation.cantor");
    assert_ne!(out.code, 0, "should refuse to run:\n{}", out.stdout);
    assert!(
        out.stdout.contains("counterexample  main"),
        "expected a counterexample for main:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected a domain-violation reason:\n{}",
        out.stdout
    );
}

#[test]
fn string_literal_concat_of_two_bare_literals() {
    // Regression test: `++` on two bare Tuple literals with no already-
    // Vector operand (`kind::ConcatMerge::CoerceBothToVector`) — previously
    // an unconditional `scalarize_to_int` call in `compile_binop` crashed on
    // any multi-field Tuple operand before `++`'s own dispatch ever ran.
    let out = run_subcommand("string_literal_concat.cantor");
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
