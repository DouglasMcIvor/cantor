//! The check-worker protocol, exercised against the real binary.
//!
//! `check_file` runs cvc5 in a subprocess so a wedged solve can be killed,
//! and talks to it over newline-delimited JSON on stdout. These tests drive
//! that protocol directly rather than through `check_file`, so a break in the
//! wire format is reported as a protocol failure rather than as every solver
//! test failing at once.

use std::io::Write as _;
use std::process::Stdio;

use cantor::{
    parser::parse_file,
    solver::{
        CheckOutcome, CheckResult,
        worker::{Message, Request, WORKER_ARG},
    },
};

use super::helpers::cantor;

/// Run the worker over `src` and return everything it wrote, in order.
fn worker_messages(src: &str) -> Vec<Message> {
    let request = Request {
        items: parse_file(src).expect("parse"),
        timeout_ms: 60_000,
    };

    let mut child = cantor()
        .arg(WORKER_ARG)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&request).expect("serialize request"))
        .expect("write request");

    let out = child.wait_with_output().expect("wait for worker");
    assert!(
        out.status.success(),
        "worker exited {:?}: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );

    // Anything cvc5 itself prints to stdout is not our protocol; the
    // supervisor skips unparseable lines and so does this.
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .collect()
}

#[test]
fn worker_reports_progress_then_a_final_verdict() {
    let messages = worker_messages(
        "\
inc : Nat -> Nat
inc(x) = x + 1
",
    );

    let (last, rest) = messages.split_last().expect("at least one message");
    assert!(
        matches!(last, Message::Done(_)),
        "last message must be Done, got {last:?}"
    );
    assert!(
        !rest.is_empty() && rest.iter().all(|m| matches!(m, Message::Progress { .. })),
        "expected progress messages before Done, got {rest:?}"
    );
}

/// The label is what lets a killed worker name the obligation that hung,
/// rather than failing the whole file anonymously.
#[test]
fn progress_messages_name_the_obligation_in_flight() {
    let messages = worker_messages(
        "\
inc : Nat -> Nat
inc(x) = x + 1
",
    );

    let labels: Vec<&str> = messages
        .iter()
        .filter_map(|m| match m {
            Message::Progress { label } => label.as_deref(),
            Message::Done(_) => None,
        })
        .collect();
    assert!(
        labels.contains(&"inc"),
        "expected a heartbeat labelled `inc`, got {labels:?}"
    );
}

/// A fully-proved file's `ConstrainedTree` is what codegen consumes, so it
/// has to arrive intact — not just a verdict that it proved.
#[test]
fn worker_returns_a_usable_constrained_tree() {
    let messages = worker_messages(
        "\
inc : Nat -> Nat
inc(x) = x + 1
",
    );

    let Some(Message::Done(outcome)) = messages.last() else {
        panic!("expected a Done message");
    };
    match outcome.as_ref() {
        Ok(CheckOutcome::Proved(tree)) => {
            assert_eq!(tree.items.len(), 1);
            assert!(!tree.sem_items.is_empty());
            assert!(!tree.overflow_checks.is_empty());
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

/// A counterexample has to survive the trip too — it's the report a user
/// actually reads.
#[test]
fn worker_reports_counterexamples() {
    let messages = worker_messages(
        "\
bad : Int -> Nat
bad(x) = x - 1
",
    );

    let Some(Message::Done(outcome)) = messages.last() else {
        panic!("expected a Done message");
    };
    match outcome.as_ref() {
        Ok(CheckOutcome::NotProved(results)) => {
            assert!(matches!(
                results[0].1[0].1,
                CheckResult::Counterexample { .. }
            ));
        }
        other => panic!("expected NotProved, got {other:?}"),
    }
}

/// A malformed request is a bug in the supervisor, not in the user's
/// program — it must fail loudly rather than exit 0 having checked nothing.
#[test]
fn worker_rejects_a_malformed_request() {
    let mut child = cantor()
        .arg(WORKER_ARG)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn worker");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"not json")
        .expect("write request");

    let out = child.wait_with_output().expect("wait for worker");
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("malformed request"));
}
