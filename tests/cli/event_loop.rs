//! MVP IO event loop (docs/design-decisions.md §6) — `cantor run` end to end.

use super::helpers::*;

#[test]
fn event_loop_echoes_lines_with_persisted_state() {
    let out = run_subcommand_with_stdin("event_loop_echo.cantor", "a\nb\nc\n");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    // `state` starts at 0 and increments once per call, including the final
    // synthetic EOT call after `c` — so the visible counter goes 0,1,2 across
    // the three real lines, plus one more (invisible, EOT-prefixed) line.
    assert!(
        out.stdout.contains("a:0\nb:1\nc:2\n"),
        "expected echoed lines with a persisted counter:\n{}",
        out.stdout
    );
    let lines: Vec<&str> = out.stdout.lines().collect();
    assert!(
        lines.last().unwrap().ends_with(":3"),
        "expected one extra line for the EOT-triggered final call:\n{}",
        out.stdout
    );
}

#[test]
fn event_loop_runs_once_for_eot_on_immediate_eof() {
    // `run_subcommand`'s stdin is closed immediately (no lines piped at
    // all) — the driver must still make exactly one call, with the
    // synthetic EOT `Event`, using the seeded initial `State`.
    let out = run_subcommand("event_loop_echo.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    let lines: Vec<&str> = out.stdout.lines().collect();
    assert!(
        lines.last().unwrap().ends_with(":0"),
        "expected exactly one EOT-triggered call against the seeded state:\n{}",
        out.stdout
    );
}

#[test]
fn missing_seed_overload_is_a_compile_error() {
    let out = run_file("event_loop_missing_seed.cantor");
    assert_ne!(out.code, 0, "should refuse to compile:\n{}", out.stdout);
    assert!(
        out.stderr.contains("event-loop `main`")
            && out.stderr.contains("zero-argument `main : -> Digit`"),
        "expected the missing-seed diagnostic:\n{}",
        out.stderr
    );
}

#[test]
fn mismatched_state_identifiers_is_a_compile_error() {
    let out = run_file("event_loop_mismatched_state.cantor");
    assert_ne!(out.code, 0, "should refuse to compile:\n{}", out.stdout);
    assert!(
        out.stderr.contains("event-loop `main`")
            && out.stderr.contains("domain has `Digit`, range has `Other`"),
        "expected the mismatched-state-identifier diagnostic:\n{}",
        out.stderr
    );
}
