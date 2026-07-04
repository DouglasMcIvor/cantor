//! Shared `parse → check_names → check_file` orchestration.
//!
//! `main.rs` (whole-file batch check) and `repl.rs` (incremental,
//! definition-at-a-time check) drive the same underlying pieces but react to
//! failures differently — a naming error is fatal for `main.rs` but only
//! rejects one definition in the REPL, and only `main.rs`'s `run` subcommand
//! cares about `CheckOutcome::Proved`'s `ConstrainedTree` at all. So this
//! module doesn't force one flow onto both call sites; it only pulls out the
//! two pieces that were byte-for-byte identical wherever they occurred: the
//! parse+naming gate, and unwrapping a `CheckOutcome` down to its
//! per-signature results.

use crate::ast::Item;
use crate::error::CompileError;
use crate::names::check_names;
use crate::parser::parse_file;
use crate::solver::{CheckOutcome, CheckResult};

/// Everything that can go wrong before `check_file` ever gets to run the
/// solver: a parse error, or one or more naming-convention violations.
pub enum FrontendError {
    Parse(CompileError),
    Naming(Vec<CompileError>),
}

/// Parse `src` and reject it if `check_names` finds any violations — the
/// common prefix of every caller that parses a file and immediately needs
/// well-named items before doing anything else with them.
pub fn parse_and_check_names(src: &str) -> Result<Vec<Item>, FrontendError> {
    let items = parse_file(src).map_err(FrontendError::Parse)?;
    let naming_errors = check_names(&items);
    if !naming_errors.is_empty() {
        return Err(FrontendError::Naming(naming_errors));
    }
    Ok(items)
}

/// Flatten a `CheckOutcome` to its per-signature results regardless of
/// whether the file as a whole was fully proved — callers that just want to
/// display or inspect results don't care which arm produced them, only
/// `main.rs`'s `run` subcommand needs the `ConstrainedTree` itself.
pub fn results_of(outcome: &CheckOutcome) -> &[(String, Vec<(String, CheckResult)>)] {
    match outcome {
        CheckOutcome::Proved(tree) => &tree.results,
        CheckOutcome::NotProved(results) => results,
    }
}
