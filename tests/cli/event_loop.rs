//! MVP IO event loop (docs/design-decisions.md §6) — `cantor run` end to end.

use super::helpers::*;

#[test]
fn event_loop_survives_many_arena_resets() {
    // Arena memory plan (see `cantor-runtime/src/arena.rs`'s module doc):
    // every step swaps in a fresh arena, deep-copies State's leaves into it,
    // then drops the arena the step actually ran in. A handful of lines (the
    // other tests in this file) wouldn't catch a bug that only corrupts
    // State after several swap/copy/drop cycles in a row — this drives 100.
    let input: String = (0..100).map(|i| format!("{i}\n")).collect();
    let out = run_subcommand_with_stdin("event_loop_echo.cantor", &input);
    assert_eq!(
        out.code, 0,
        "expected exit 0:\n{}\n{}",
        out.stdout, out.stderr
    );
    // `cantor run` prints a proof-report header before the event loop's own
    // output — take just the echoed lines (the last 101: 100 real lines
    // plus the final EOT-triggered call), same as `lines.last()` elsewhere
    // in this file, just checking every line instead of only the last one.
    let all_lines: Vec<&str> = out.stdout.lines().collect();
    assert!(
        all_lines.len() >= 101,
        "expected at least 101 lines:\n{}",
        out.stdout
    );
    let lines = &all_lines[all_lines.len() - 101..];
    for (i, line) in lines.iter().enumerate() {
        let expected_suffix = format!(":{}", i % 10);
        assert!(
            line.ends_with(&expected_suffix),
            "line {i} = {line:?}, expected suffix {expected_suffix:?}\nfull output:\n{}",
            out.stdout
        );
    }
}

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

// ── Output shape gate: Char* is no longer the only Output Kind that proves,
// but only Char* is wired into the driver yet ────────────────────────────

#[test]
fn image_output_shape_proves_fine() {
    // The shape gate (`wire::is_event_loop_step_shape`) no longer requires
    // Output to be `Char*` — a compound `Image` Output proves like any other
    // Kind. Whether `cantor run`/`cantor build` can actually *drive* it is a
    // separate, later question (see `image_output_run_refuses_cleanly`
    // below) — this test is just "the solver doesn't reject the shape".
    let out = run_file("event_loop_image_output.cantor");
    assert_eq!(
        out.code, 0,
        "event_loop_image_output.cantor check should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}",
        out.stdout
    );
}

#[test]
fn image_output_run_refuses_cleanly() {
    // `cantor run`'s driver only marshals `Char*` Output so far (the
    // cantor-runtime/wasm.rs generalization is later work) — a proved
    // Image-output program must be refused with a clear diagnostic, not
    // silently miscompiled or crash as an ICE.
    let out = run_subcommand("event_loop_image_output.cantor");
    assert_ne!(
        out.code, 0,
        "should refuse to run:\n{}\n{}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("not yet supported") && out.stderr.contains("Char*"),
        "expected a clear not-yet-supported diagnostic, not an ICE:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
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
