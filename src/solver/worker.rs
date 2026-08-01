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
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use super::{CheckOutcome, CheckResult};
use crate::ast::Item;
use crate::error::CompileError;

/// Set to any non-empty value to run the solver in this process instead of a
/// worker, losing the ability to kill a wedged solve. For attaching a
/// debugger or a profiler, where a second process is in the way.
pub const INPROCESS_ENV: &str = "CANTOR_INPROCESS_SOLVER";

/// Overrides worker discovery with an explicit path to a `cantor` binary.
pub const WORKER_ENV: &str = "CANTOR_CHECK_WORKER";

/// Overrides how long a worker may go without reporting progress before it is
/// assumed wedged and killed. See [`progress_budget`].
pub const BUDGET_ENV: &str = "CANTOR_PROGRESS_BUDGET_MS";

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

// ── The supervising half ─────────────────────────────────────────────────────

/// How long the supervisor waits for a worker to make *any* progress before
/// concluding it is wedged, given a `tlimit` of `timeout_ms`.
///
/// Deliberately looser than `tlimit` itself. When cvc5 does honour its own
/// limit it produces a far better result than a kill can — a per-signature
/// `Unknown` with the rest of the file still checked — so the supervisor
/// should only fire for queries that have blown through `tlimit` entirely.
/// The floor covers the two gaps that aren't a solver query at all:
/// elaboration before the first check-sat, and building the result after the
/// last one. Both are fast, but the floor also has to absorb a heavily loaded
/// machine — a budget tight enough to trip under parallel test load would turn
/// a safety net into a source of spurious `Unknown`s.
///
/// [`BUDGET_ENV`] overrides the result outright, for a machine slow enough to
/// need more headroom than the floor gives, and for tests that would otherwise
/// have to wait it out.
fn progress_budget(timeout_ms: u64) -> Duration {
    if let Some(override_ms) = std::env::var(BUDGET_ENV)
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        return Duration::from_millis(override_ms);
    }
    Duration::from_millis((timeout_ms * 2).max(10_000))
}

/// Locate a `cantor` binary to run as the worker.
///
/// `current_exe` is the obvious candidate but is only correct when the
/// running process *is* the compiler. The solver is also linked into test
/// binaries, which cargo puts one directory deeper (`target/debug/deps/`)
/// than the binary itself, so a sibling lookup covers that case.
fn worker_exe() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os(WORKER_ENV) {
        return Some(PathBuf::from(explicit));
    }

    let exe = std::env::current_exe().ok()?;
    let name = format!("cantor{}", std::env::consts::EXE_SUFFIX);
    if exe.file_name().is_some_and(|f| f == name.as_str()) {
        return Some(exe);
    }

    let dir = exe.parent()?;
    [dir.join(&name), dir.parent()?.join(&name)]
        .into_iter()
        .find(|candidate| candidate.is_file())
}

/// Everything a killed check still knows: which obligation was in flight.
fn timed_out(label: Option<String>, budget: Duration) -> CheckOutcome {
    let subject = label.unwrap_or_else(|| "the file".to_owned());
    let reason = format!(
        "solver timed out — no progress for {}s while checking `{subject}`, so the check \
         worker was killed. cvc5's own `tlimit` does not reliably interrupt every query \
         shape; raise `--timeout` if this obligation just needs longer.",
        budget.as_secs()
    );
    CheckOutcome::NotProved(vec![(
        subject.clone(),
        vec![(subject, CheckResult::Unknown(reason))],
    )])
}

/// Kill `child` and reap it, so a wedged worker can't outlive the compiler.
fn terminate(mut child: Child) {
    let _ = child.kill();
    let _ = child.wait();
}

/// Run the check in a worker process, killing it if it stops making progress.
///
/// Returns `Unknown` rather than a verdict when that happens, per CLAUDE.md's
/// rule that the compiler never assumes what it hasn't proved: a killed check
/// has proved nothing, and must not be mistaken for one that passed.
pub(super) fn supervise(
    items: &[Item],
    timeout_ms: u64,
) -> Result<CheckOutcome, crate::error::CompileError> {
    let exe = worker_exe().ok_or_else(|| {
        CompileError::ice(format!(
            "could not locate a `cantor` binary to run the check worker; \
             set {WORKER_ENV} to its path, or {INPROCESS_ENV}=1 to check in-process"
        ))
    })?;

    let mut child = Command::new(&exe)
        .arg(WORKER_ARG)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| CompileError::ice(format!("could not start check worker {exe:?}: {e}")))?;

    // Both pipes get their own thread. The request can be larger than a pipe
    // buffer and the worker starts replying before it has read all of it, so
    // writing and reading from one thread can deadlock with each side waiting
    // on the other.
    let request = Request {
        items: items.to_vec(),
        timeout_ms,
    };
    let mut stdin = child.stdin.take().expect("stdin was piped");
    std::thread::spawn(move || {
        let _ = serde_json::to_writer(&mut stdin, &request);
    });

    let stdout = child.stdout.take().expect("stdout was piped");
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines().map_while(Result::ok) {
            // Anything cvc5 prints on stdout is not part of the protocol.
            if let Ok(message) = serde_json::from_str::<Message>(&line)
                && tx.send(message).is_err()
            {
                return;
            }
        }
    });

    // `--timeout 0` means "no limit", and that has to apply to the supervisor
    // too — otherwise it would reimpose the very limit the user opted out of.
    let budget = (timeout_ms > 0).then(|| progress_budget(timeout_ms));
    let mut label = None;
    loop {
        let received = match budget {
            Some(budget) => rx.recv_timeout(budget).map_err(|e| e.to_string()),
            None => rx.recv().map_err(|e| e.to_string()),
        };
        match received {
            Ok(Message::Progress { label: current }) => label = current,
            Ok(Message::Done(outcome)) => {
                terminate(child);
                return *outcome;
            }
            // Timed out, or the worker died without reporting. The latter is
            // a crash (a cvc5 segfault, an OOM kill); neither has proved
            // anything, so both surface as `Unknown`.
            Err(_) => {
                let status = child.try_wait().ok().flatten();
                terminate(child);
                return Ok(match (budget, status) {
                    (Some(budget), None) => timed_out(label, budget),
                    _ => CheckOutcome::NotProved(vec![(
                        "the file".to_owned(),
                        vec![(
                            "the file".to_owned(),
                            CheckResult::Unknown(format!(
                                "the check worker exited without reporting a result ({}) — \
                                 nothing in this file has been verified",
                                match status {
                                    Some(status) => status.to_string(),
                                    None => "still running".to_owned(),
                                }
                            )),
                        )],
                    )]),
                });
            }
        }
    }
}
