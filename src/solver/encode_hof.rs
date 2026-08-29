//! Encoding for calls through first-class function values (higher-order
//! functions v0, backlog.md).
//!
//! Split out of `encode_call.rs` as a pure refactor (no behaviour change) to
//! keep that file under the repo's line-count guideline — same reason
//! `encode_call.rs` itself was split out of `encode.rs`.

use std::collections::HashMap;

use cvc5::{Sort, Term, TermManager};

use crate::{
    ast::BinOp,
    semantics::tree::{SemExpr, SemExprKind, SemFunctionDef, SemFunctionSig},
    span::Symbol,
};

use super::encode::{EncodeCtx, Env, encode_expr, mk_decomposed_tuple};
use super::encode_call::{
    CallSite, DomainMatch, assert_call_contract, assert_domain_implies_membership, sig_domain_match,
};
use super::membership::{Membership, membership_constraint};
use super::obligations::BuiltinObligation;
use super::sort::{
    extract_success_value, is_product_range, maybe_coerce, set_sort, success_arm_of_range,
};

/// Encode a call through a first-class function value: `arrow` is the
/// `SemExprKind::BinOp { op: Arrow, lhs, rhs }` node the *enclosing*
/// function's own signature declared for this parameter (e.g. `apply`'s own
/// `f : (Int -> Int)`) — `lhs` is trusted as `f`'s domain, `rhs` as its
/// range, reusing `sig_domain_match`/`assert_call_contract` exactly as an
/// ordinary named call does, just against a synthesized single-signature
/// `SemFunctionSig` instead of a globally-declared one.
///
/// **What this proves:** given `f : (Int -> Int)` as a fact from the
/// enclosing signature, a call `f(x)` inside that function's body is
/// checked/contracted like any other call — trusting `f`'s declared
/// contract. That trust is only sound because of the *other* half of this
/// story, `function_value_arg_membership` below: at every call site that
/// passes a concrete function in (`apply(double, 5)`), the passed
/// function's own declared domain/range is checked structurally against
/// what the parameter declared, so `f`'s contract can never be trusted
/// here without having been earned there.
pub(super) fn encode_function_value_call<'tm>(
    arrow: &SemExpr,
    call: &CallSite<'_>,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
    coerce_to: Option<Sort<'tm>>,
    narrow_try: bool,
) -> Result<Term<'tm>, String> {
    let CallSite {
        callee,
        args,
        span: call_span,
    } = *call;
    let SemExprKind::BinOp {
        op: BinOp::Arrow,
        lhs: domain,
        rhs: range,
    } = &arrow.kind
    else {
        return Err(format!(
            "call to function value `{}` has a malformed declared Kind (internal error)",
            callee.0
        ));
    };
    let sig = SemFunctionSig {
        domain: Some(domain.as_ref().clone()),
        range: range.as_ref().clone(),
        param_kinds: Vec::new(),
        return_kind: range.kind_of.clone(),
        span: call_span,
    };

    let arg_terms: Vec<Term<'_>> = args
        .iter()
        .map(|a| encode_expr(a, env, ctx, path_cond.clone(), None))
        .collect::<Result<_, _>>()?;

    match sig_domain_match(&sig, args, &arg_terms, callee, ctx)? {
        DomainMatch::Mismatch => {
            return Err(format!(
                "call to function value `{}` has the wrong arity for its declared Kind \
                 (internal error)",
                callee.0
            ));
        }
        DomainMatch::Trivial => {}
        DomainMatch::Constrained(obligation) => {
            ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation,
                violated_reason: format!(
                    "arguments to `{}` are not in its declared domain",
                    callee.0
                ),
            });
        }
    }

    let fresh = format!("_call_{}", *ctx.call_counter);
    *ctx.call_counter += 1;
    let result_var = if is_product_range(&sig.range) {
        let (assembled, leaves) = mk_decomposed_tuple(
            ctx.tm,
            &fresh,
            &sig.range,
            ctx.distinct_preds,
            ctx.name_defs,
        );
        for (leaf, leaf_set) in leaves {
            if let Membership::Constrained(c) =
                membership_constraint(ctx.tm, leaf, leaf_set, ctx.name_defs, ctx.distinct_preds)
            {
                ctx.solver.assert_formula(c);
            }
        }
        assembled
    } else {
        match set_sort(ctx.tm, &sig.range, ctx.distinct_preds, ctx.name_defs) {
            Some(sort) => ctx.tm.mk_const(sort, &fresh),
            None => {
                return Err(format!(
                    "call to function value `{}` has an unsupported range sort (internal error)",
                    callee.0
                ));
            }
        }
    };

    assert_call_contract(&sig, &arg_terms, result_var.clone(), ctx);
    if narrow_try && let Some(success) = success_arm_of_range(&sig.range) {
        assert_domain_implies_membership(&sig, &arg_terms, result_var.clone(), success, ctx);
    }

    if narrow_try {
        let success = success_arm_of_range(&sig.range).ok_or_else(|| {
            format!(
                "`?` used on a call to function value `{}`, whose range has no success arm \
                 to narrow to",
                callee.0
            )
        })?;
        return extract_success_value(
            ctx.tm,
            result_var,
            success,
            ctx.distinct_preds,
            ctx.name_defs,
        )
        .ok_or_else(|| {
            format!(
                "cannot narrow `?` on call to function value `{}`: the success arm's shape \
                 doesn't resolve to a single extraction from its range's datatype",
                callee.0
            )
        });
    }

    maybe_coerce(ctx.tm, result_var, &coerce_to)
}

// ── Call-site check: a concrete function passed into a function-Kind param ──

/// Whether a call argument that's a bare reference to a real, declared
/// function (`arg`) satisfies a function-Kind parameter's declared
/// `Domain -> Range` (`part`) — the other half of higher-order-functions
/// v0's soundness story from `encode_function_value_call` above. That
/// function trusts `f`'s declared contract *inside* the body that received
/// it; this function is what makes trusting it sound: at the call site that
/// actually passes a concrete function in (`apply(double, 5)`), `double`'s
/// own declared domain/range must genuinely match what `apply` declared for
/// `f`, or the trust inside `apply`'s body would be unearned.
///
/// Per the user's explicit choice (2026-08-29 design discussion): **exact
/// structural Set match**, not real variance/subtyping — deliberately out
/// of scope, avoids needing a new subset-proof solver query for something
/// that's otherwise a purely syntactic comparison. `sem_expr_structural_eq`
/// does the comparison; this function is just the "is `arg` even a
/// comparable shape" gate around it (a bare `Var` naming a real,
/// non-overloaded-or-single-bucket function — anything else, e.g. a call
/// result or a local, isn't resolvable to a concrete declared signature
/// here, so this honestly reports `Unsupported` rather than guessing).
///
/// Returns `Membership::Constrained(true/false)` when the comparison is
/// fully decidable (a hard fact, not a solver query — see
/// `sem_expr_structural_eq`), or `Unsupported` when `arg`/`part` aren't in
/// a shape this can compare at all — propagates to `Unknown` at the call
/// site, same as any other not-yet-supported domain shape.
pub(super) fn function_value_arg_membership<'tm>(
    tm: &'tm TermManager,
    arg: &SemExpr,
    part: &SemExpr,
    fn_env: &HashMap<Symbol, Vec<&SemFunctionDef>>,
) -> Membership<'tm> {
    let SemExprKind::BinOp {
        op: BinOp::Arrow,
        lhs: param_domain,
        rhs: param_range,
    } = &part.kind
    else {
        return Membership::Unsupported;
    };
    let SemExprKind::Var(sym) = &arg.kind else {
        return Membership::Unsupported;
    };
    // Single-signature names only, even though an eligible *overloaded*
    // name (elaborate::expr's `Var` arm — every candidate agreeing on
    // `(param_kinds, return_kind)`) can equally be a `Kind::Function`
    // value: its candidates agree on *Kind*, not on their individually
    // declared domain *Sets* (that's exactly what makes them different
    // overloads — e.g. `Nat` vs `Int - Nat`), so comparing structurally
    // against any *one* candidate's domain would be comparing against the
    // wrong thing (the true declared domain is their union, which a purely
    // structural, semantics-free comparison can't check without real set
    // reasoning — the "no new solver machinery" line this function's doc
    // comment draws). Falling through to `Unsupported`/`Unknown` here is
    // conservative in the safe direction (never a false counterexample,
    // never a false proof) — confirmed as a real bug during development:
    // comparing against `defs.first()` alone produced a false
    // counterexample for a legitimately-covering overloaded value.
    let Some([def]) = fn_env.get(sym).map(Vec::as_slice) else {
        return Membership::Unsupported;
    };
    let Some(sig) = def.sigs.first() else {
        return Membership::Unsupported;
    };
    let Some(arg_domain) = sig.domain.as_ref() else {
        return Membership::Unsupported;
    };
    let domain_eq = sem_expr_structural_eq(arg_domain, param_domain);
    let range_eq = sem_expr_structural_eq(&sig.range, param_range);
    match (domain_eq, range_eq) {
        (Some(true), Some(true)) => Membership::Constrained(tm.mk_boolean(true)),
        (Some(false), _) | (_, Some(false)) => Membership::Constrained(tm.mk_boolean(false)),
        _ => Membership::Unsupported,
    }
}

/// Structural (syntactic) equality of two Set-expression `SemExpr` trees,
/// ignoring spans and `kind_of` — used only by
/// `function_value_arg_membership` above. **Exact match, not semantic
/// equivalence**: `Nat` and `Int - {n for n in Int if n < 0}` denote the
/// same set but compare unequal here (`Some(false)`, since they're
/// different shapes at different variants) — a real, accepted limitation
/// of the "exact structural match" scope (see this module's doc comment),
/// not a bug.
///
/// `None` for any shape not handled below (rare in a domain/range
/// annotation — e.g. `Comprehension`, `Tuple`, a literal) rather than
/// guessing either way; callers treat `None` as `Unsupported`/`Unknown`.
fn sem_expr_structural_eq(a: &SemExpr, b: &SemExpr) -> Option<bool> {
    use SemExprKind as K;
    match (&a.kind, &b.kind) {
        (K::Var(x), K::Var(y)) => Some(x == y),
        (K::DisjointUnion(a1, a2), K::DisjointUnion(b1, b2))
        | (K::SetDifference(a1, a2), K::SetDifference(b1, b2))
        | (K::CartesianProduct(a1, a2), K::CartesianProduct(b1, b2)) => {
            Some(sem_expr_structural_eq(a1, b1)? && sem_expr_structural_eq(a2, b2)?)
        }
        (K::SetQuotient(a1, ac), K::SetQuotient(b1, bc)) => {
            Some(ac == bc && sem_expr_structural_eq(a1, b1)?)
        }
        (
            K::BinOp {
                op: op_a,
                lhs: a1,
                rhs: a2,
            },
            K::BinOp {
                op: op_b,
                lhs: b1,
                rhs: b2,
            },
        ) => {
            Some(op_a == op_b && sem_expr_structural_eq(a1, b1)? && sem_expr_structural_eq(a2, b2)?)
        }
        (K::SetLit(xs), K::SetLit(ys)) => {
            if xs.len() != ys.len() {
                return Some(false);
            }
            xs.iter().zip(ys).try_fold(true, |acc, (x, y)| {
                Some(acc && sem_expr_structural_eq(x, y)?)
            })
        }
        (K::KleeneStar(a1), K::KleeneStar(b1)) => sem_expr_structural_eq(a1, b1),
        (
            K::Call {
                callee: ca,
                args: aa,
            },
            K::Call {
                callee: cb,
                args: ab,
            },
        ) => {
            if ca != cb || aa.len() != ab.len() {
                return Some(false);
            }
            aa.iter().zip(ab).try_fold(true, |acc, (x, y)| {
                Some(acc && sem_expr_structural_eq(x, y)?)
            })
        }
        // Different top-level shapes — under exact structural matching
        // (not semantic equivalence), always a definite mismatch, never
        // Unknown: both trees are fully known at compile time, so which
        // variant each is is itself already a decided fact.
        _ if std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind) => Some(false),
        _ => None,
    }
}
