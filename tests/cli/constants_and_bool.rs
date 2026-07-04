use super::helpers::*;

// ── Constants ─────────────────────────────────────────────────────────────────

#[test]
fn const_demo_proves_and_runs() {
    // const_demo.cantor defines `base : Nat = 10` and `tau : Nat = 2 * 314`,
    // then uses them in a function; main() should return 638.
    let out = run_subcommand("const_demo.cantor");
    assert_eq!(out.code, 0, "expected exit 0:\n{}\n{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("638"),
        "expected main() = 638 in output:\n{}", out.stdout
    );
}

#[test]
fn const_demo_shows_proved_for_constants() {
    let out = run_subcommand("const_demo.cantor");
    assert!(
        out.stdout.contains("base : Nat = 10"),
        "expected constant display in output:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("4 proved"),
        "expected 4 proved in summary:\n{}", out.stdout
    );
}

// ── Bool domain and range ─────────────────────────────────────────────────────

#[test]
fn bool_demo_all_proved() {
    let out = run_file("bool_demo.cantor");
    assert_eq!(out.code, 0, "bool_demo.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample result line:\n{}", out.stdout
    );
}

#[test]
fn bool_demo_shows_bool_signatures() {
    let out = run_file("bool_demo.cantor");
    assert!(out.stdout.contains("Int -> Bool"), "expected 'Int -> Bool' sig:\n{}", out.stdout);
    assert!(out.stdout.contains("Bool -> Bool"), "expected 'Bool -> Bool' sig:\n{}", out.stdout);
    assert!(out.stdout.contains("Bool -> Nat"),  "expected 'Bool -> Nat' sig:\n{}", out.stdout);
}

#[test]
fn bool_run_executes_and_prints_result() {
    // negate(is_positive(-3)) = negate(false) = true, so main() = 99
    let out = run_subcommand("bool_run.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 99"),
        "expected 'main() = 99' in output:\n{}", out.stdout
    );
}

#[test]
fn bool_run_proves_all_sigs() {
    let out = run_subcommand("bool_run.cantor");
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
}
