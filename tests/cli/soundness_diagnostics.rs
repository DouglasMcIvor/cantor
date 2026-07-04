use super::helpers::*;

// ── Call-site domain obligations (end-to-end) ─────────────────────────────────

#[test]
fn call_domain_violation_counterexample() {
    // `bad(x) = safe_div(x, 0)` violates safe_div's `Int - {0}` domain: the
    // call site must fail to prove, or a proved program divides by zero.
    let out = run_file("call_domain_violation.cantor");
    assert_ne!(
        out.code, 0,
        "call_domain_violation.cantor should exit non-zero:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  bad"),
        "expected counterexample for bad:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("not in its declared domain"),
        "expected call-site domain reason:\n{}",
        out.stdout
    );
}

#[test]
fn call_domain_violation_callee_still_proved() {
    // safe_div itself is fine — only the caller is at fault.
    let out = run_file("call_domain_violation.cantor");
    assert!(
        out.stdout.contains("proved          safe_div"),
        "expected safe_div proved:\n{}",
        out.stdout
    );
}

#[test]
fn require_after_call_proved() {
    // `require y in Nat` depends on non_neg's own contract (result ∈ Nat).
    // check_require used to run in a solver seeded only from a separately
    // threaded fact list that never saw call contracts (those are asserted
    // straight onto the main solver) — so this used to report a spurious
    // counterexample.
    let out = run_file("require_after_call.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("proved          after_call"),
        "expected after_call proved:\n{}",
        out.stdout
    );
}

#[test]
fn loop_body_obligation_counterexample() {
    // Division by zero inside a while body, feeding a variable whose `Int`
    // invariant imposes no constraint — previously proved, then SIGFPE'd
    // under `cantor run`.
    let out = run_file("loop_body_obligation.cantor");
    assert_ne!(
        out.code, 0,
        "loop_body_obligation.cantor should exit non-zero:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  h"),
        "expected counterexample for h:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("division by zero"),
        "expected division-by-zero reason:\n{}",
        out.stdout
    );
}

// ── Non-integer block locals (end-to-end) ──────────────────────────────────────

#[test]
fn bool_tuple_lets_prove_and_run() {
    // Bool and tuple `let`s in block bodies used to abort the cvc5 process
    // (integer-sorted SSA constants); now they prove and execute.
    let out = run_subcommand("bool_tuple_lets.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("main() = 42"),
        "expected 'main() = 42' in output:\n{}",
        out.stdout
    );
}

// ── Cross-kind comparison diagnostics (end-to-end) ─────────────────────────────

#[test]
fn kind_mismatch_eq_clean_error() {
    // `x == true` with x : Int used to reach cvc5 as an ill-sorted term and
    // abort with a raw C++ error; now it's a Cantor diagnostic.
    let out = run_file("kind_mismatch_eq.cantor");
    assert_ne!(
        out.code, 0,
        "kind_mismatch_eq.cantor should exit non-zero:\n{}",
        out.stdout
    );
    assert!(
        out.stderr.contains("same value family"),
        "expected operand-family diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("cvc5"),
        "must not leak a raw cvc5 abort:\n{}",
        out.stderr
    );
}
