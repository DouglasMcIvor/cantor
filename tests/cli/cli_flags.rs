use super::helpers::*;

// ── Bracket-depth newlines ────────────────────────────────────────────────────

#[test]
fn newline_paren_all_proved() {
    // Regression: bare ident at end of assignment followed by ( on the next line
    // must not be parsed as a function call (old bug: `b := tmp\n(a,b)` → `b := tmp(a,b)`).
    let out = run_file("newline_paren.cantor");
    assert_eq!(
        out.code, 0,
        "newline_paren.cantor should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected no failures:\n{}",
        out.stdout
    );
}

#[test]
fn newline_paren_run_produces_correct_output() {
    let out = run_subcommand("newline_paren.cantor");
    assert_eq!(
        out.code, 0,
        "newline_paren.cantor run should exit 0\nstdout: {}",
        out.stdout
    );
    // swap_test((-3, 7)) = (7, -3); main returns x + y = 7 + (-3) = 4
    assert!(
        out.stdout.contains("4"),
        "expected output 4 from newline_paren.cantor main:\n{}",
        out.stdout
    );
}

// ── --timeout flag ────────────────────────────────────────────────────────────

#[test]
fn timeout_flag_space_form_is_accepted() {
    let out = run(&["--timeout", "30", fixture("good.cantor").to_str().unwrap()]);
    assert_eq!(
        out.code, 0,
        "--timeout 30 should succeed\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("proved"),
        "expected proved output:\n{}",
        out.stdout
    );
}

#[test]
fn timeout_flag_equals_form_is_accepted() {
    let out = run(&["--timeout=10", fixture("good.cantor").to_str().unwrap()]);
    assert_eq!(
        out.code, 0,
        "--timeout=10 should succeed\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("proved"),
        "expected proved output:\n{}",
        out.stdout
    );
}

#[test]
fn timeout_flag_zero_disables_limit() {
    let out = run(&["--timeout=0", fixture("good.cantor").to_str().unwrap()]);
    assert_eq!(
        out.code, 0,
        "--timeout=0 should succeed\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("proved"),
        "expected proved output:\n{}",
        out.stdout
    );
}

#[test]
fn timeout_flag_missing_value_errors() {
    let out = run(&["--timeout"]);
    assert_ne!(out.code, 0, "missing --timeout value should fail");
    assert!(
        out.stderr.contains("--timeout requires a value"),
        "expected error message:\n{}",
        out.stderr
    );
}

#[test]
fn timeout_flag_non_integer_errors() {
    let out = run(&["--timeout", "abc", fixture("good.cantor").to_str().unwrap()]);
    assert_ne!(out.code, 0, "non-integer --timeout should fail");
    assert!(
        out.stderr.contains("non-negative integer"),
        "expected error message:\n{}",
        out.stderr
    );
}
