//! `ConstrainedTree` — a strict proof-gate wrapper around an elaborated file.
//!
//! Only ever constructed by `check_file` when every obligation in the file
//! resolved to `CheckResult::Proved`. Its existence *is* the proof — there's
//! no way to obtain one that skips checking.

use crate::{ast::Item, semantics::tree::SemItem, solver::CheckResult};

/// An elaborated file that has been fully verified: every signature's
/// domain/range obligations proved, no unproved constructs anywhere.
///
/// Carries both the raw `items` and the elaborated `sem_items` so that
/// `codegen::compile_constrained` can compile from `sem_items` without
/// re-running `elaborate()`, while still having `items` available for the
/// (deliberately AST-level) constant-folding pass in `codegen::compile_items`.
pub struct ConstrainedTree {
    pub items: Vec<Item>,
    pub sem_items: Vec<SemItem>,
    /// Every entry's every `CheckResult` is `CheckResult::Proved` — kept
    /// around so callers can still display a per-signature proof report
    /// without recomputing anything.
    pub results: Vec<(String, Vec<(String, CheckResult)>)>,
}
