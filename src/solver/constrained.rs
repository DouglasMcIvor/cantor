//! `ConstrainedTree` — a strict proof-gate wrapper around an elaborated file.
//!
//! Only ever constructed by `check_file` when every obligation in the file
//! resolved to `CheckResult::Proved`. Its existence *is* the proof — there's
//! no way to obtain one that skips checking.

use std::collections::HashMap;

use crate::{ast::Item, semantics::tree::SemItem, solver::CheckResult, span::Span};

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
    /// int-soundness-plan phase 1: per-arithmetic-node-span "result fits in
    /// Int64" verdicts. Deliberately *not* part of the proof this type
    /// represents — an absent or `false` entry means codegen must emit a
    /// checked instruction + runtime abort, never a compile error. Keyed by
    /// the arithmetic expression's own span (`Add`/`Sub`/`Mul`/`Div`/unary
    /// `Neg`); consulted only by `codegen::compile_constrained`.
    pub overflow_checks: HashMap<Span, bool>,
    /// int-soundness-plan phase 2: per-call-node-span statically-resolved
    /// overload index, keyed the same way codegen's mangled-name table is
    /// (position in file order within the whole same-name `Vec<SemFunctionDef>`).
    /// Also *not* part of the proof this type represents — an absent entry
    /// means codegen must emit a runtime membership-test dispatch chain
    /// instead of a direct call; it's an optimization side-channel, never a
    /// soundness requirement (the call's domain-membership obligation is
    /// proved unconditionally, regardless of whether resolution succeeded).
    pub overload_resolution: HashMap<Span, usize>,
}
