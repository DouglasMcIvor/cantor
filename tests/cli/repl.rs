use super::helpers::*;

// ── No-arg / REPL ────────────────────────────────────────────────────────────

#[test]
fn no_args_starts_repl_and_exits_cleanly_on_eof() {
    let out = run_repl("");
    assert_eq!(out.code, 0, "REPL should exit 0 on EOF, got: {out:?}");
    assert!(
        out.stdout.contains("Goodbye"),
        "expected goodbye message, got stdout: {:?}", out.stdout
    );
}

#[test]
fn repl_quit_command_exits_cleanly() {
    let out = run_repl(":quit\n");
    assert_eq!(out.code, 0, "expected exit 0 after :quit");
}

#[test]
fn repl_help_command_shows_commands() {
    let out = run_repl(":help\n:quit\n");
    assert!(
        out.stdout.contains(":quit"),
        "expected :help to list :quit, got: {:?}", out.stdout
    );
}

#[test]
fn repl_set_alias_reports_defined() {
    // Unannotated set aliases have nothing to verify; the REPL reports "defined".
    let out = run_repl("Colour = {1, 2, 3}\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("defined"),
        "expected 'defined' for set alias, got: {:?}", out.stdout
    );
}

#[test]
fn repl_annotated_definition_shows_proved() {
    // A function with a signature gets verified immediately.
    // The sig and implementation are entered over two lines (multi-line input).
    let out = run_repl("double : Int -> Int\ndouble(x) = x * 2\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("proved"),
        "expected 'proved' for annotated function, got: {:?}", out.stdout
    );
}

#[test]
fn repl_expression_evaluation_returns_result() {
    let out = run_repl("1 + 1\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains('2'),
        "expected result 2, got: {:?}", out.stdout
    );
}

#[test]
fn repl_defs_command_lists_definitions() {
    let out = run_repl("double : Int -> Int\ndouble(x) = x * 2\n:defs\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("double"),
        "expected :defs to list 'double', got: {:?}", out.stdout
    );
}

#[test]
fn repl_reset_clears_definitions() {
    let out = run_repl("double : Int -> Int\ndouble(x) = x * 2\n:reset\n:defs\n:quit\n");
    assert_eq!(out.code, 0);
    assert!(
        out.stdout.contains("no definitions"),
        "expected no definitions after :reset, got: {:?}", out.stdout
    );
}

#[test]
fn repl_bad_args_prints_usage() {
    let out = run(&["run"]);
    assert_eq!(out.code, 2, "expected exit 2 for bad args");
    assert!(out.stderr.contains("usage"), "expected usage on stderr");
}
