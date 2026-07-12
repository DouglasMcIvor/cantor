//! MVP IO event loop (docs/design-decisions.md §6): validates the shape of
//! an event-loop-style `main` — a 2-arity overload `Char* * S -> Char* * S`
//! paired with a 0-arity `main : -> S` seed — before `check_file` hands
//! control to the ordinary per-signature domain/range checker.
//!
//! This is a structural/shape check, not a proof obligation: there is
//! nothing for cvc5 to prove here (no domain/range containment claim), so
//! it reports a hard `CompileError` and short-circuits `check_file` rather
//! than producing a `CheckResult` — the same way `sem_param_set_exprs`'s
//! arity mismatch is a hard error, not something the solver adjudicates.

use crate::error::CompileError;
use crate::kind::Kind as ValKind;
use crate::semantics::tree::{
    SemExpr, SemExprKind, SemFunctionDef, flatten_cartesian_product, sem_param_set_exprs,
};
use crate::span::Symbol;

use super::FunctionEnv;

/// True when a Kind is exactly `Char*` (`Vector(Char)`) — the fixed v0
/// Event/Output shape (docs/design-decisions.md §6). Event/Output aren't
/// required to be spelled via a named alias (a bare `Char*` literal is the
/// common case), so unlike State below, this is a Kind check only.
fn is_char_star(kind: &ValKind) -> bool {
    matches!(kind, ValKind::Vector(elem) if **elem == ValKind::Char)
}

/// One `main` signature whose shape matches the event-loop pattern
/// `Char* * S -> Char* * S`. Carries the raw domain/range State
/// sub-expressions (not just `Kind`) because the identifier-equality check
/// below compares *names* — `Kind` alone can't distinguish two different
/// named sets that happen to share a representation (e.g. two `Int`-Kind
/// sets), which is exactly the case this check exists to catch.
struct EventLoopCandidate<'a> {
    domain_state: &'a SemExpr,
    range_state: &'a SemExpr,
}

/// Find the (at most one, for v0) 2-arity `main` signature shaped like
/// `Char* * S -> Char* * S`, across every `main` `SemFunctionDef`/`sigs`
/// entry. Returns `Ok(None)` when no `main` looks like an event loop at all
/// — an ordinary 2-arg function named `main` with an unrelated domain isn't
/// `cantor run`'s concern, mirroring today's rule that only a 0-arg `main`
/// is runnable at all.
fn find_event_loop_candidate<'a>(
    main_defs: &[&'a SemFunctionDef],
) -> Result<Option<EventLoopCandidate<'a>>, CompileError> {
    let mut candidates: Vec<EventLoopCandidate<'a>> = Vec::new();
    for def in main_defs {
        if def.params.len() != 2 {
            continue;
        }
        for sig in &def.sigs {
            if sig.param_kinds.len() != 2 || !is_char_star(&sig.param_kinds[0]) {
                continue;
            }
            let ValKind::Tuple(range_elems) = &sig.return_kind else {
                continue;
            };
            if range_elems.len() != 2 || !is_char_star(&range_elems[0]) {
                continue;
            }
            let Some(domain) = sig.domain.as_ref() else {
                continue;
            };
            // Both sides must actually flatten to 2 parts — guards against
            // e.g. a domain whose Kind coincidentally lines up but whose
            // shape doesn't (sem_param_set_exprs already enforces this for
            // `param_kinds`, but `sig.range` has no such check yet).
            if sem_param_set_exprs(Some(domain), 2).is_err() {
                continue;
            }
            let domain_parts = flatten_cartesian_product(domain);
            let range_parts = flatten_cartesian_product(&sig.range);
            if domain_parts.len() != 2 || range_parts.len() != 2 {
                continue;
            }
            candidates.push(EventLoopCandidate {
                domain_state: domain_parts[1],
                range_state: range_parts[1],
            });
        }
    }
    match candidates.len() {
        0 => Ok(None),
        1 => Ok(candidates.into_iter().next()),
        _ => Err(CompileError::EventLoopMainShape {
            detail: "multiple `main` overloads match the event-loop shape \
                     `Char* * S -> Char* * S` — only one is supported"
                .to_string(),
            span: candidates[1].domain_state.span,
        }),
    }
}

/// Pull the bare identifier out of a State sub-expression, or report why it
/// can't be used as State: v0 requires a named set (`MyState = ...`), not
/// an anonymous inline set expression, since the whole point of this check
/// is comparing *names* across three positions.
fn state_identifier(expr: &SemExpr) -> Result<&Symbol, CompileError> {
    match &expr.kind {
        SemExprKind::Var(sym) => Ok(sym),
        _ => Err(CompileError::EventLoopMainShape {
            detail: "the State component of an event-loop `main` must be a named set \
                     (e.g. `MyState = Int * Int`), not an anonymous set expression"
                .to_string(),
            span: expr.span,
        }),
    }
}

/// Validate the event-loop `main` contract, if the file defines one at all.
/// No-op (`Ok(())`) when `main` has no 2-arity `Char* * S -> Char* * S`
/// overload — such a file just isn't using the event-loop feature, and the
/// existing zero-arg-`main` `cantor run` path is unaffected.
pub(super) fn validate_event_loop_main(fn_env: &FunctionEnv<'_>) -> Result<(), CompileError> {
    let main_sym = Symbol::new("main");
    let Some(main_defs) = fn_env.get(&main_sym) else {
        return Ok(());
    };

    let Some(candidate) = find_event_loop_candidate(main_defs)? else {
        return Ok(());
    };

    let domain_state = state_identifier(candidate.domain_state)?;
    let range_state = state_identifier(candidate.range_state)?;

    if domain_state != range_state {
        return Err(CompileError::EventLoopMainShape {
            detail: format!(
                "State must be the same named set in both positions — \
                 domain has `{domain_state}`, range has `{range_state}`"
            ),
            span: candidate.range_state.span,
        });
    }

    // Require a matching 0-arity seed: `main : -> S` for the same `S`,
    // reusing ordinary overload-by-arity (§7) rather than a new binding
    // convention. Default-construction of State is deliberately not
    // supported yet (docs/design-decisions.md §6) — no fallback here.
    let has_seed = main_defs.iter().any(|def| {
        def.params.is_empty()
            && def.sigs.iter().any(|sig| {
                sig.domain.is_none()
                    && matches!(&sig.range.kind, SemExprKind::Var(sym) if sym == domain_state)
            })
    });

    if !has_seed {
        return Err(CompileError::EventLoopMainShape {
            detail: format!(
                "requires a zero-argument `main : -> {domain_state}` overload to seed \
                 State (default-construction of an arbitrary set is not yet implemented)"
            ),
            span: candidate.domain_state.span,
        });
    }

    Ok(())
}
