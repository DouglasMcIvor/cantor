use super::helpers::*;

// ── Missing file ──────────────────────────────────────────────────────────────

#[test]
fn missing_file_exits_nonzero() {
    let out = run(&["/nonexistent/cantor_file.cantor"]);
    assert_ne!(out.code, 0, "expected non-zero exit for missing file");
    assert!(!out.stderr.is_empty(), "expected error message on stderr");
}

// ── Parse errors ──────────────────────────────────────────────────────────────

#[test]
fn parse_error_exits_nonzero() {
    let out = run_file("parse_error.cantor");
    assert_ne!(out.code, 0, "expected non-zero exit for parse error");
}

#[test]
fn parse_error_message_goes_to_stderr() {
    let out = run_file("parse_error.cantor");
    assert!(
        !out.stderr.is_empty(),
        "expected parse error on stderr, stdout was: {:?}", out.stdout
    );
}

// ── Good file: all proved ─────────────────────────────────────────────────────

#[test]
fn good_file_exits_zero() {
    let out = run_file("good.cantor");
    assert_eq!(out.code, 0, "good.cantor should exit 0\nstdout: {}", out.stdout);
}

#[test]
fn good_file_reports_proved_for_every_function() {
    let out = run_file("good.cantor");
    // abs, double, quad — all should be proved.
    for name in &["abs", "double", "quad"] {
        assert!(
            out.stdout.contains(name),
            "expected `{name}` in output:\n{}", out.stdout
        );
    }
    // Match the indented result-line prefix, not just the bare word
    // (the summary "0 counterexample(s)" also contains "counterexample").
    assert!(
        out.stdout.contains("  proved  "),
        "expected '  proved  ' result line in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample result line in output:\n{}", out.stdout
    );
}

#[test]
fn good_file_summary_line() {
    let out = run_file("good.cantor");
    // Summary should show 3 proved and no failures.
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("0 counterexample"),
        "expected '0 counterexample' in summary:\n{}", out.stdout
    );
}

#[test]
fn good_file_shows_signatures() {
    // The signature of each function should appear in the output.
    let out = run_file("good.cantor");
    assert!(out.stdout.contains("Int -> Nat"),  "abs sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("Nat -> Nat"),  "double/quad sig missing:\n{}", out.stdout);
}

// ── Bad file: counterexamples ─────────────────────────────────────────────────

#[test]
fn bad_file_exits_nonzero() {
    let out = run_file("bad.cantor");
    assert_ne!(out.code, 0, "bad.cantor should exit non-zero\nstdout: {}", out.stdout);
}

#[test]
fn bad_file_reports_counterexamples() {
    let out = run_file("bad.cantor");
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved result line in output:\n{}", out.stdout
    );
}

#[test]
fn bad_file_summary_line() {
    let out = run_file("bad.cantor");
    assert!(
        out.stdout.contains("0 proved"),
        "expected '0 proved' in summary:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("2 counterexample"),
        "expected '2 counterexample' in summary:\n{}", out.stdout
    );
}

#[test]
fn counterexample_output_shows_witness_and_range() {
    // The output should tell the developer what values caused the violation
    // and which range was not satisfied.
    let out = run_file("bad.cantor");
    assert!(
        out.stdout.contains("->  output ="),
        "expected witness format 'x = N  ->  output = M':\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("not in"),
        "expected 'not in <Range>' in output:\n{}", out.stdout
    );
    // Specific range names should appear.
    assert!(out.stdout.contains("Int16"), "expected Int16 range:\n{}", out.stdout);
    assert!(out.stdout.contains("Nat"),   "expected Nat range:\n{}", out.stdout);
}
