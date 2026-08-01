//! What happens when the solver doesn't come back.
//!
//! cvc5 ignores `tlimit` for some query shapes and its Rust binding has no
//! `interrupt()`, so the check runs in a worker process the compiler can
//! kill. These tests cover the two ways that can end — killed for making no
//! progress, and dying without reporting — and pin the property that matters
//! in both: an unfinished check reports `unknown` and exits non-zero. Anything
//! that let it read as `proved` would be a silent false proof.

use std::process::Command;

use super::helpers::{Output, cantor, fixture};

/// `run`, but with environment overrides — the timeout knobs are only
/// reachable through the environment.
fn run_with_env(args: &[&str], env: &[(&str, &str)]) -> Output {
    let mut cmd: Command = cantor();
    cmd.args(args);
    for (key, value) in env {
        cmd.env(key, value);
    }
    let out = cmd.output().expect("failed to spawn cantor binary");
    Output {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code().unwrap_or(-1),
    }
}

fn check_hang_fixture(env: &[(&str, &str)]) -> Output {
    let path = fixture("solver_hang_kleene_loop.cantor");
    run_with_env(&["--timeout", "1", path.to_str().unwrap()], env)
}

/// The headline behaviour: a solve that ignores `tlimit` is killed, and the
/// compiler returns instead of hanging with it.
#[test]
fn a_wedged_solver_is_killed_and_reported_as_unknown() {
    // Well under the real floor, which exists to tolerate a loaded machine
    // rather than to make anyone wait for it. See `worker::progress_budget`.
    let out = check_hang_fixture(&[("CANTOR_PROGRESS_BUDGET_MS", "1500")]);

    assert!(
        out.stdout.contains("unknown"),
        "expected an unknown result, got:\n{}{}",
        out.stdout,
        out.stderr
    );
    // Also the canary for the fixture itself: this can only appear if the
    // worker really was killed, so if cvc5 ever starts answering the query
    // this fails rather than passing vacuously. See the fixture for what to
    // do about that.
    assert!(
        out.stdout.contains("solver timed out"),
        "the timeout should be explained, got:\n{}",
        out.stdout
    );
    assert_ne!(out.code, 0, "an unproved file must not exit successfully");
    assert!(
        !out.stdout.contains("proved          "),
        "a killed check must never report a proof:\n{}",
        out.stdout
    );
}

/// A killed check has to say *which* obligation hung — that's the whole
/// reason the worker reports progress per query rather than just staying
/// alive.
#[test]
fn a_killed_check_names_the_obligation_that_hung() {
    let out = check_hang_fixture(&[("CANTOR_PROGRESS_BUDGET_MS", "1500")]);
    assert!(
        out.stdout.contains("grow"),
        "expected the hung obligation to be named, got:\n{}",
        out.stdout
    );
}

/// A worker that dies without reporting (a cvc5 segfault, an OOM kill) has
/// proved exactly as much as one that hung: nothing.
#[test]
fn a_worker_that_dies_without_reporting_is_not_a_pass() {
    let path = fixture("good.cantor");
    let out = run_with_env(
        &[path.to_str().unwrap()],
        &[("CANTOR_CHECK_WORKER", "/bin/false")],
    );

    assert!(
        out.stdout.contains("unknown"),
        "expected an unknown result, got:\n{}{}",
        out.stdout,
        out.stderr
    );
    assert!(
        out.stdout.contains("without reporting a result"),
        "the failure should be explained, got:\n{}",
        out.stdout
    );
    assert_ne!(out.code, 0);
}

/// A worker binary that can't be found is an environment problem, and has to
/// be reported as one — never quietly downgraded to an in-process check that
/// can't be killed.
#[test]
fn a_missing_worker_binary_is_a_loud_error() {
    let path = fixture("good.cantor");
    let out = run_with_env(
        &[path.to_str().unwrap()],
        &[("CANTOR_CHECK_WORKER", "/nonexistent/cantor")],
    );

    assert_ne!(out.code, 0);
    assert!(
        out.stderr.contains("check worker"),
        "expected an error naming the worker, got:\n{}",
        out.stderr
    );
    // A broken environment is the user's to fix, so it must not be dressed up
    // as an internal compiler error — see `CompileError`'s taxonomy.
    assert!(
        !out.stderr.contains("file an issue") && !out.stderr.contains("internal compiler error"),
        "an environment problem must not be reported as a compiler bug:\n{}",
        out.stderr
    );
}

/// The debugging escape hatch still checks the file properly — it only gives
/// up the ability to kill a wedged solve.
#[test]
fn the_in_process_escape_hatch_still_checks() {
    let path = fixture("good.cantor");
    let out = run_with_env(
        &[path.to_str().unwrap()],
        &[("CANTOR_INPROCESS_SOLVER", "1")],
    );

    assert_eq!(out.code, 0, "expected a clean check, got:\n{}", out.stderr);
    assert!(out.stdout.contains("proved"), "got:\n{}", out.stdout);
}
