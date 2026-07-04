use super::helpers::*;

// ── Tuples / anonymous product types ──────────────────────────────────────────

#[test]
fn tuple_basics_all_proved() {
    let out = run_file("tuple_basics.cantor");
    assert_eq!(out.code, 0, "tuple_basics.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("5 proved"),
        "expected '5 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn tuple_basics_shows_product_signatures() {
    let out = run_file("tuple_basics.cantor");
    assert!(out.stdout.contains("Int * Int -> Int"), "fst/snd sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("Nat * Nat -> Nat"), "sum_pair sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("Int * Int -> Int * Int"), "swap/identity sig missing:\n{}", out.stdout);
}

#[test]
fn tuple_run_prints_tuple_result() {
    // swap((3, 9)) = (9, 3)
    let out = run_subcommand("tuple_run.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = (9, 3)"),
        "expected 'main() = (9, 3)' in output:\n{}", out.stdout
    );
}

#[test]
fn tuple_run_proves_all_sigs() {
    let out = run_subcommand("tuple_run.cantor");
    assert!(
        out.stdout.contains("2 proved"),
        "expected '2 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn tuple_bad_counterexample() {
    // overflow_pair : Int16 * Int16 -> Int16 overflows when both elements are large.
    let out = run_file("tuple_bad.cantor");
    assert_ne!(out.code, 0, "tuple_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved line:\n{}", out.stdout
    );
}

#[test]
fn tuple_bad_counterexample_mentions_range() {
    let out = run_file("tuple_bad.cantor");
    assert!(
        out.stdout.contains("not in Int16"),
        "expected 'not in Int16' in counterexample output:\n{}", out.stdout
    );
}

// ── Destructuring ─────────────────────────────────────────────────────────────

#[test]
fn destructure_basics_all_proved() {
    let out = run_file("destructure_basics.cantor");
    assert_eq!(out.code, 0, "destructure_basics.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected no failures:\n{}", out.stdout
    );
}

#[test]
fn destructure_basics_run_produces_correct_output() {
    let out = run_subcommand("destructure_basics.cantor");
    assert_eq!(out.code, 0, "destructure_basics.cantor run should exit 0\nstdout: {}", out.stdout);
    // main() returns -3 + 4 = 1
    assert!(
        out.stdout.contains("1"),
        "expected output 1 from destructure_basics.cantor main:\n{}", out.stdout
    );
}

#[test]
fn destructure_bad_gives_counterexample() {
    let out = run_file("destructure_bad.cantor");
    assert_ne!(out.code, 0, "destructure_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
}

#[test]
fn destructure_mut_run_produces_correct_output() {
    let out = run_subcommand("destructure_mut.cantor");
    assert_eq!(out.code, 0, "destructure_mut.cantor run should exit 0\nstdout: {}", out.stdout);
    // main() computes (-3 + 4) + (4 + -3) = 1 after swap; a+b = 4 + (-3) = 1
    assert!(
        out.stdout.contains("1"),
        "expected output 1 from destructure_mut.cantor main:\n{}", out.stdout
    );
}

#[test]
fn destructure_partial_all_proved() {
    let out = run_file("destructure_partial.cantor");
    assert_eq!(out.code, 0, "destructure_partial.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected no failures:\n{}", out.stdout
    );
}

#[test]
fn destructure_partial_run_produces_correct_output() {
    let out = run_subcommand("destructure_partial.cantor");
    assert_eq!(out.code, 0, "destructure_partial.cantor run should exit 0\nstdout: {}", out.stdout);
    // main() returns 1 + 2 + 3 = 6
    assert!(
        out.stdout.contains("6"),
        "expected output 6 from destructure_partial.cantor main:\n{}", out.stdout
    );
}

// ── Vector destructuring: not yet implemented ────────────────────────────────
//
// The README documents `h, t = v` for a vector `v` (head elements plus a
// vector tail, proof-gated on `v` having enough elements) — none of
// elaborate/solver/codegen support this yet. Both statement forms must
// report it clearly (a "not yet implemented" `CompileError`/`Unknown`) —
// never a raw cvc5 abort or a misleading generic "wrong shape" message.

#[test]
fn vector_destructure_let_clean_error() {
    let out = run_file("vector_destructure_let.cantor");
    assert_ne!(out.code, 0, "vector_destructure_let.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stderr.contains("not yet implemented") && out.stderr.contains("vector"),
        "expected a 'not yet implemented' vector-destructuring diagnostic on stderr:\n{}", out.stderr
    );
}

#[test]
fn vector_param_destructure_clean_error() {
    // `foo(x, y)` on a `Nat* - {[]}` domain — same underlying gap, reached via
    // function-parameter arity disambiguation instead of a `let`/`:=` statement.
    let out = run_file("vector_param_destructure.cantor");
    assert_ne!(out.code, 0, "vector_param_destructure.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stderr.contains("isn't supported yet") && out.stderr.contains("vector"),
        "expected a vector-destructuring hint on stderr:\n{}", out.stderr
    );
}

#[test]
fn vector_destructure_assign_clean_error() {
    // Previously a raw `cvc5: error: index out of bound` process abort — the
    // vector RHS is an opaque integer term with no children in the solver,
    // and `DestructAssign` unconditionally called `child()` on it.
    let out = run_file("vector_destructure_assign.cantor");
    assert!(
        out.stdout.contains("unknown         f"),
        "expected an Unknown result for f, not a crash:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("cvc5") && !out.stderr.contains("cvc5"),
        "must not leak a raw cvc5 abort:\nstdout: {}\nstderr: {}", out.stdout, out.stderr
    );
}
