//! Proof obligations produced while encoding expressions, and how they're decided.
//!
//! Kept separate from `encode.rs`'s actual "SemExpr → cvc5 Term" recursion:
//! this module answers *what must be proved* (the built-in operator domain
//! table, the obligation record types) and *how it's decided once collected*
//! (`decide_overflow_obligations`/`decide_overload_resolutions`), while
//! `encode.rs` only calls into it as it walks the tree.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{BinOp, UnOp},
    semantics::tree::SemExpr,
    span::Span,
};

use super::CheckResult;
use super::blocks::check_require;

/// A proof obligation produced when encoding a built-in operator argument.
///
/// The caller asserts `path_cond → obligation` and, on a SAT result,
/// inspects the model to report `violated_reason` in the counterexample.
pub(crate) struct BuiltinObligation<'tm> {
    pub(crate) path_cond: Term<'tm>,
    pub(crate) obligation: Term<'tm>,
    pub(crate) violated_reason: String,
}

/// A "this arithmetic result fits in Int64" obligation produced when encoding
/// `Add`/`Sub`/`Mul`/`Div`/unary `Neg`.
///
/// Kept entirely separate from `BuiltinObligation`/`builtin_obligs`: unlike
/// those (which gate the file-wide proof — see `ConstrainedTree`'s doc
/// comment), an unproved overflow obligation must *not* block compilation
/// (docs/int-soundness-plan.md phase 1's explicit requirement — proved i64
/// overflow is a runtime concern, not a compile error). Decided independently
/// via `check_require` after body encoding finishes, and the per-span outcome
/// is stashed on `ConstrainedTree::overflow_checks` purely for codegen to
/// consult — it never feeds `CheckResult`/`CheckOutcome`.
pub(crate) struct OverflowObligation<'tm> {
    pub(crate) span: Span,
    pub(crate) path_cond: Term<'tm>,
    pub(crate) obligation: Term<'tm>,
}

/// A "which overload does this call resolve to" obligation, produced by
/// `encode_call` (int-soundness-plan phase 2) only when the callee's
/// overload set has more than one candidate at the call's arity.
///
/// Like `OverflowObligation`, this is an optimization side-channel, not a
/// soundness requirement: the call's domain obligation (that the arguments
/// lie in *some* candidate's domain — asserted unconditionally, unaffected
/// by this) already guarantees correctness. Deciding which one is proved is
/// purely so codegen can emit a direct call instead of a runtime dispatch
/// chain; failing to resolve is always safe (falls back to runtime
/// dispatch), never a compile error.
pub(crate) struct OverloadCallObligation<'tm> {
    pub(crate) call_span: Span,
    pub(crate) path_cond: Term<'tm>,
    /// `(overload_index, "args ∈ this overload's domain")`, indexed the same
    /// way `codegen`'s mangled-name table is: position in file order within
    /// the whole same-name `Vec<&SemFunctionDef>`.
    pub(crate) candidates: Vec<(usize, Term<'tm>)>,
}

/// Decide every collected overflow obligation against `solver` via
/// `check_require` (seeds a fresh solver from `solver`'s current assertions,
/// negates, checks) — must run *before* the caller's own correctness check
/// asserts its negated goal onto `solver`, since that assertion (once the
/// correctness claim is proved) leaves `solver` with an inconsistent
/// assertion set, under which every later query is vacuously "proved".
///
/// Merges into `overflow_checks` with `&=` — a span reached more than once
/// (e.g. a multi-signature function's shared body, or a loop's condition and
/// body both referencing the same node) is only elided when every reaching
/// path proves it, since codegen still compiles one shared body.
pub(crate) fn decide_overflow_obligations<'tm>(
    overflow_obligs: &[OverflowObligation<'tm>],
    tm: &'tm TermManager,
    solver: &Solver<'tm>,
    overflow_checks: &mut HashMap<Span, bool>,
    timeout_ms: u64,
) {
    for ob in overflow_obligs {
        let implication = if ob.path_cond.to_string().trim() == "true" {
            ob.obligation.clone()
        } else {
            tm.mk_term(
                Kind::Implies,
                &[ob.path_cond.clone(), ob.obligation.clone()],
            )
        };
        let proved = matches!(
            check_require(implication, tm, solver, &[], &[], timeout_ms),
            CheckResult::Proved
        );
        overflow_checks
            .entry(ob.span)
            .and_modify(|p| *p &= proved)
            .or_insert(proved);
    }
}

/// Decide every collected overload-call obligation against `solver`, same
/// timing rule as `decide_overflow_obligations` (before the caller's own
/// negated-goal assertion). For each obligation, tries every candidate in
/// order and records the first one whose `path_cond → args ∈ domain_i` is
/// provable via `check_require`.
///
/// Merges into `overload_resolutions` by requiring unanimous agreement
/// across every reaching path (`None` on any disagreement) rather than
/// `&=`: a shared body is checked once per signature and, for loops, once
/// per inductive-step call, but a *specific* resolved index (not a boolean)
/// is only trustworthy for codegen — which compiles that call site exactly
/// once — when every path that reaches it agrees on the same overload. A
/// span absent from every reaching obligation set (this obligation is the
/// first entry seen for it) starts at whatever that first path resolved.
pub(crate) fn decide_overload_resolutions<'tm>(
    overload_obligs: &[OverloadCallObligation<'tm>],
    tm: &'tm TermManager,
    solver: &Solver<'tm>,
    overload_resolutions: &mut HashMap<Span, Option<usize>>,
    timeout_ms: u64,
) {
    for ob in overload_obligs {
        let mut resolved: Option<usize> = None;
        for (idx, candidate) in &ob.candidates {
            let implication = if ob.path_cond.to_string().trim() == "true" {
                candidate.clone()
            } else {
                tm.mk_term(Kind::Implies, &[ob.path_cond.clone(), candidate.clone()])
            };
            if matches!(
                check_require(implication, tm, solver, &[], &[], timeout_ms),
                CheckResult::Proved
            ) {
                resolved = Some(*idx);
                break;
            }
        }
        overload_resolutions
            .entry(ob.call_span)
            .and_modify(|p| {
                if *p != resolved {
                    *p = None;
                }
            })
            .or_insert(resolved);
    }
}

/// Domain constraints for argument `arg_idx` (0-based) of a binary built-in.
///
/// Returns a list of `(set, reason)` pairs; each pair generates a proof obligation
/// that the argument belongs to `set`.  An empty list means unconstrained.
/// Multiple constraints are checked independently (e.g. the `/` divisor needs
/// both `Int` and `NonZeroInt`).
///
/// `In`/`NotIn` are handled by early-return paths before this is called —
/// passing either here is a programming error and will panic.
pub(crate) fn binary_builtin_domain(op: &BinOp, arg_idx: usize) -> Vec<(SemExpr, &'static str)> {
    match (op, arg_idx) {
        // ── Arithmetic ────────────────────────────────────────────────────────
        // Div arg 1: divisor must be a plain Int AND non-zero.
        (BinOp::Div, 1) => vec![
            (
                named_set("Int"),
                "divisor must be Int, not a member of a distinct set",
            ),
            (named_set("NonZeroInt"), "division by zero"),
        ],
        // All arithmetic args must be plain Int (not Bool, not a distinct set).
        (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div, _) => vec![(
            named_set("Int"),
            "operand must be Int, not a member of a distinct set",
        )],
        // ── Comparisons ───────────────────────────────────────────────────────
        (BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge, _) => vec![],
        // ── Logical ───────────────────────────────────────────────────────────
        // Both args of `and`/`or` must be in Bool.
        (BinOp::And | BinOp::Or, _) => vec![(
            named_set("Bool"),
            "operand of logical operator must be Bool",
        )],
        // ── Set operations ────────────────────────────────────────────────────
        (BinOp::Union | BinOp::Intersect | BinOp::SymDiff, _) => vec![],
        // ── Vector operations ─────────────────────────────────────────────────
        // `++` operands must be vectors; their element sorts are checked by CVC5.
        (BinOp::Concat, _) => vec![],
        // ── Must never reach here ─────────────────────────────────────────────
        (BinOp::In | BinOp::NotIn, _) => {
            panic!(
                "binary_builtin_domain called with In/NotIn — handled before the domain-check loop"
            )
        }
    }
}

/// Domain constraints for the operand of a unary built-in.
///
/// Returns a list of `(set, reason)` pairs; empty means unconstrained.
pub(crate) fn unary_builtin_domain(op: &UnOp) -> Vec<(SemExpr, &'static str)> {
    match op {
        // Negation is defined on Int only — distinct sets cannot be negated.
        UnOp::Neg => vec![(
            named_set("Int"),
            "operand of negation must be Int, not a member of a distinct set",
        )],
        // Operand of `not` must be in Bool.
        UnOp::Not => vec![(named_set("Bool"), "operand of `not` must be Bool")],
    }
}

/// Build a `Var` expression that refers to a named built-in set.
pub(crate) fn named_set(name: &'static str) -> SemExpr {
    let kind = crate::semantics::builtins::lookup(name)
        .map(|b| b.kind)
        .unwrap_or(crate::kind::Kind::Int);
    SemExpr::var(name, kind)
}
