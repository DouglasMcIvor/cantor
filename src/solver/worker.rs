//! The check worker — cvc5 behind a process boundary.
//!
//! cvc5's `tlimit` option is not reliably honoured: several query shapes run
//! indefinitely past it (see the hang notes in docs/design-decisions.md), and
//! the Rust binding exposes no `interrupt()`. Killing a process is therefore
//! the only mechanism that can actually stop a wedged solve, so `check_file`
//! runs the whole check in a subprocess — this module is the protocol between
//! the two halves.
//!
//! The request is the parsed file; the response is a stream of newline-
//! delimited JSON [`Message`]s on stdout, terminated by a [`Message::Done`]
//! carrying the entire result. Everything in between is a [`Message::Progress`],
//! emitted immediately before each cvc5 check-sat.
//!
//! **Why progress messages rather than a single deadline.** A file's check is
//! many hundreds of individual queries, and a whole-file deadline can't tell
//! "one wedged query" apart from "a large file legitimately taking a while".
//! Watching for progress instead keeps the supervisor's timeout per-query,
//! matching what `tlimit` was always meant to mean, and the label each message
//! carries names the obligation that was in flight — so a hang reports which
//! signature caused it rather than failing the file anonymously.

use std::cell::RefCell;
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};

use serde::{Deserialize, Serialize};

use super::CheckOutcome;
use crate::ast::Item;
use crate::error::CompileError;

/// The argv marker that turns `cantor` into a check worker. Deliberately
/// ugly: it's an internal calling convention between two copies of the
/// compiler, not a user-facing subcommand.
pub const WORKER_ARG: &str = "__check-worker";

/// Written to the worker's stdin as a single JSON value, followed by EOF.
#[derive(Debug, Serialize, Deserialize)]
pub struct Request {
    pub items: Vec<Item>,
    pub timeout_ms: u64,
}

/// Written to the worker's stdout, one JSON value per line.
#[derive(Debug, Serialize, Deserialize)]
pub enum Message {
    /// About to enter cvc5. `label` names the obligation being checked, or is
    /// `None` for work that isn't attributable to a single signature.
    Progress { label: Option<String> },
    /// Terminal message — the complete result of the check.
    Done(Box<Result<CheckOutcome, CompileError>>),
}

/// Whether this process is a worker. Governs whether [`emit_progress`] writes
/// anything at all: the same solver code runs in-process for
/// `CANTOR_INPROCESS_SOLVER`, where stdout belongs to the user and a stray
/// heartbeat would be corruption rather than protocol.
static IS_WORKER: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// The obligation currently being checked. Ambient rather than a
    /// parameter because the alternative is threading a label that only the
    /// heartbeat reads through 11 call sites across six modules — every one
    /// of which would then be a place to forget it.
    static CURRENT_LABEL: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Run `f` with `label` as the obligation reported by any heartbeat it emits,
/// restoring the previous label afterwards. Restoring rather than clearing
/// matters: a stale label would misattribute a hang to whichever signature
/// happened to finish last.
pub(super) fn with_label<T>(label: &str, f: impl FnOnce() -> T) -> T {
    let previous = CURRENT_LABEL.with(|l| l.borrow_mut().replace(label.to_owned()));
    let result = f();
    CURRENT_LABEL.with(|l| *l.borrow_mut() = previous);
    result
}

/// Announce that a cvc5 check-sat is about to start. Called from
/// `sig_check::checked_sat`, which every query in the crate routes through.
pub(super) fn emit_progress() {
    if !IS_WORKER.load(Ordering::Relaxed) {
        return;
    }
    let label = CURRENT_LABEL.with(|l| l.borrow().clone());
    emit(&Message::Progress { label });
}

fn emit(msg: &Message) {
    let mut out = std::io::stdout().lock();
    // A broken pipe here means the supervisor gave up on us and is about to
    // deliver a kill; there is nobody left to report the failure to.
    if serde_json::to_writer(&mut out, msg).is_ok() {
        let _ = out.write_all(b"\n");
        let _ = out.flush();
    }
}

/// Worker entry point: read the request, run the check, report, exit.
///
/// Never returns — a worker process does exactly one check. That's what makes
/// dropping the old process-wide cvc5 mutex safe: each check gets a fresh
/// single-threaded process, so cvc5's thread-unsafe global state has no other
/// caller to race with.
pub fn run() -> ! {
    let request: Request = match serde_json::from_reader(std::io::stdin().lock()) {
        Ok(request) => request,
        Err(e) => {
            eprintln!("cantor {WORKER_ARG}: malformed request: {e}");
            std::process::exit(2);
        }
    };

    IS_WORKER.store(true, Ordering::Relaxed);
    let outcome = super::check_file_in_process(&request.items, request.timeout_ms);
    emit(&Message::Done(Box::new(outcome)));
    std::process::exit(0)
}
