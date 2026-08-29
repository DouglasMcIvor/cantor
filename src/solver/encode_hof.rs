//! Encoding for calls through first-class function values (higher-order
//! functions v0, backlog.md).
//!
//! Split out of `encode_call.rs` as a pure refactor (no behaviour change) to
//! keep that file under the repo's line-count guideline — same reason
//! `encode_call.rs` itself was split out of `encode.rs`.

use cvc5::{Sort, Term};

use crate::{
    ast::BinOp,
    semantics::tree::{SemExpr, SemExprKind, SemFunctionSig},
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
/// checked/contracted like any other call. **What this does NOT (yet)
/// prove:** that a *caller* passing a concrete function in (`apply(double,
/// 5)`) actually satisfies `f`'s declared contract — `double` isn't
/// encodable as a solver term at all yet (`Kind::Function` has no CVC5
/// sort, see `solver::sort::scalar_kind_sort`), so that call site reports
/// `Unknown` ("unbound variable `double`") independently of this function,
/// not a false `proved`. Before that gap closes, whatever change makes a
/// function-value *argument* encodable must land together with a
/// structural (exact Set match, not just Kind) check that the passed
/// function's own declared domain/range equals the parameter's declared
/// `arrow` — see backlog.md.
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

    match sig_domain_match(
        &sig,
        args,
        &arg_terms,
        callee,
        ctx.tm,
        ctx.name_defs,
        ctx.distinct_preds,
    )? {
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
