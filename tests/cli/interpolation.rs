//! String interpolation (`"a{expr}b"`, desugars to a `++`/`show(...)` chain)
//! and the builtin `show` intrinsic, end to end. See the interpolation
//! design plan and docs/design-decisions.md.

use super::helpers::*;

#[test]
fn show_scalars() {
    let out = run_subcommand("show_scalars.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 42 true x -7 7"),
        "expected each scalar Kind's display form:\n{}",
        out.stdout
    );
}

#[test]
fn show_bigint_uses_the_boxed_decimal_representation() {
    let out = run_subcommand("show_bigint.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 10223372036854775807"),
        "expected the overflowed BigInt's decimal form:\n{}",
        out.stdout
    );
}

#[test]
fn show_tuple_is_parenthesized_and_comma_separated() {
    let out = run_subcommand("show_tuple.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = (1, true, z)"),
        "expected a parenthesized tuple:\n{}",
        out.stdout
    );
}

#[test]
fn show_vector_int_is_square_bracketed() {
    let out = run_subcommand("show_vector_int.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = [1, 2, 3]"),
        "expected a square-bracketed vector:\n{}",
        out.stdout
    );
}

#[test]
fn show_nested_strings_display_bare_at_any_depth() {
    let out = run_subcommand("show_nested_vector_of_strings.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = [ab, cd]"),
        "expected bare (unquoted) strings inside the vector:\n{}",
        out.stdout
    );
}

#[test]
fn show_set_int_is_curly_braced() {
    let out = run_subcommand("show_set_int.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = {2, 3, 5}"),
        "expected a curly-braced set, distinct from Vector's brackets:\n{}",
        out.stdout
    );
}

#[test]
fn show_distinct_value_shows_its_raw_underlying_int() {
    let out = run_subcommand("show_distinct.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected the raw underlying Int (documented `distinct`-erasure limitation):\n{}",
        out.stdout
    );
}

#[test]
fn show_on_t_or_fail_success_shows_the_real_value_not_fail() {
    // Regression test: `T | Fail` shares its runtime wire shape with a
    // literal `fail`/`fail n` expression (the same `{tag, i64}` struct).
    // An earlier version of `show` assumed that shape always meant
    // failure, so a genuine success value of a `T | Fail` variable was
    // silently mis-displayed as `"fail <bits>"`.
    let out = run_subcommand("show_fail_struct_success.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected the real success value, not \"fail 5\":\n{}",
        out.stdout
    );
}

#[test]
fn show_on_t_or_fail_actual_fail_shows_fail() {
    let out = run_subcommand("show_fail_struct_fail.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = fail 0"),
        "expected a fail display with its payload:\n{}",
        out.stdout
    );
}

#[test]
fn show_on_t_or_fail_or_none_actual_none_shows_none() {
    let out = run_subcommand("show_fail_struct_none.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = none"),
        "expected a bare \"none\" display:\n{}",
        out.stdout
    );
}

#[test]
fn show_on_a_general_multi_arm_union_does_real_tag_dispatch() {
    // A genuine TaggedUnion (not the specialized `T | Fail`/`T | None` wire
    // shape) — each arm is decoded from its own leaf slots and shown with
    // its own Kind, via a real runtime branch per arm.
    let out = run_subcommand("show_tagged_union.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = (1, 2) 3"),
        "expected both arms shown with their own Kind:\n{}",
        out.stdout
    );
}

#[test]
fn show_on_a_tagged_union_nested_inside_a_tuple() {
    let out = run_subcommand("show_tagged_union_nested_in_tuple.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = ((1, 2), 3)"),
        "expected the nested union arms shown correctly inside the tuple:\n{}",
        out.stdout
    );
}

#[test]
fn interp_directly_on_a_tagged_union_variable() {
    let out = run_subcommand("interp_tagged_union.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = result: 7"),
        "expected the interpolated union value:\n{}",
        out.stdout
    );
}

#[test]
fn interp_basic_single_chunk() {
    let out = run_subcommand("interp_basic.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = hello world!"),
        "expected the interpolated greeting:\n{}",
        out.stdout
    );
}

#[test]
fn interp_multiple_chunks_left_associate() {
    let out = run_subcommand("interp_multiple_chunks.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = n=42 b=true sum=43"),
        "expected all three interpolated chunks:\n{}",
        out.stdout
    );
}

#[test]
fn interp_escaped_braces_stay_literal() {
    let out = run_subcommand("interp_escaped_braces.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = {literal} n=3"),
        "expected the escaped braces to stay literal alongside the real chunk:\n{}",
        out.stdout
    );
}
