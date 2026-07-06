//! `encode_expr`'s `if`/`.N` projection arms, and the wrapping fixed-width
//! integer (`Signed32`/`Unsigned32`) binary-operator helper `encode_binop`/
//! `encode_unop` call into.
//!
//! Split out of `encode.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — mirrors phase 1's own
//! `encode.rs` → `encode_call.rs` split.

use cvc5::{Kind, Sort, Term};

use crate::ast::BinOp;
use crate::semantics::tree::SemExpr;

use super::encode::{EncodeCtx, Env, encode_expr, proj_from_tuple};
use super::membership::{SolverPreds, WrappingInfo};
use super::obligations::BuiltinObligation;

// ── Wrapping fixed-width integers (Signed32/Unsigned32) ─────────────────────
//
// docs/wrapping-and-quotient-sets-plan.md, Feature 1. Each is its own opaque
// CVC5 sort backed by native `(_ BitVec 32)`; `+ - * neg` and ordered
// comparisons unwrap via `from_D` into BitVec land, apply the matching
// `bv*` operator, and (for `+ - * neg`) rewrap via `mk_D`. `==`/`!=` need
// none of this — plain CVC5 term equality on two same-sort terms is already
// exactly right, so `encode_binop`'s existing `Eq`/`Ne` path is untouched.

/// The registered `WrappingInfo` whose `d_sort` matches `sort`, if any.
pub(super) fn wrapping_info_for_sort<'a, 'tm>(
    distinct_preds: &'a SolverPreds<'tm>,
    sort: &Sort<'tm>,
) -> Option<&'a WrappingInfo<'tm>> {
    distinct_preds.wrapping.values().find(|i| &i.d_sort == sort)
}

/// `+ - *` and `< <= > >=` between two same-family wrapping operands.
/// Returns `None` when `l`/`r` aren't both the same registered wrapping
/// sort (caller falls through to the ordinary integer-sort path). Returns
/// `Err` for a same-sort pair whose operator isn't one of the above —
/// `/ rem quot` on a wrapping sort is explicitly out of scope for this
/// slice (division isn't a ring homomorphism mod 2^32), so it must be a
/// clean compile error, not a silently-wrong dummy value.
pub(super) fn encode_wrapping_binop<'tm>(
    op: &BinOp,
    l: &Term<'tm>,
    r: &Term<'tm>,
    ctx: &EncodeCtx<'_, 'tm>,
) -> Option<Result<Term<'tm>, String>> {
    let info = wrapping_info_for_sort(ctx.distinct_preds, &l.sort())?;
    if r.sort() != info.d_sort {
        return None;
    }
    let tm = ctx.tm;
    let bv_kind = match op {
        BinOp::Add => Kind::BitvectorAdd,
        BinOp::Sub => Kind::BitvectorSub,
        BinOp::Mul => Kind::BitvectorMult,
        BinOp::Lt => {
            if info.signed {
                Kind::BitvectorSlt
            } else {
                Kind::BitvectorUlt
            }
        }
        BinOp::Le => {
            if info.signed {
                Kind::BitvectorSle
            } else {
                Kind::BitvectorUle
            }
        }
        BinOp::Gt => {
            if info.signed {
                Kind::BitvectorSgt
            } else {
                Kind::BitvectorUgt
            }
        }
        BinOp::Ge => {
            if info.signed {
                Kind::BitvectorSge
            } else {
                Kind::BitvectorUge
            }
        }
        // `==`/`!=` need no wrapping-specific code at all (see the module
        // comment above) — return `None` so the caller's ordinary path
        // handles them with plain CVC5 term equality, unchanged.
        BinOp::Eq | BinOp::Ne => return None,
        _ => {
            return Some(Err(format!(
                "`{op}` is not yet supported between {} values — only `+ - *`, negation, \
                 and comparisons are implemented for wrapping fixed-width integers so far \
                 (division isn't a ring homomorphism mod 2^{}, deliberately deferred)",
                if info.signed {
                    "Signed32"
                } else {
                    "Unsigned32"
                },
                info.width
            )));
        }
    };
    let l_bv = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), l.clone()]);
    let r_bv = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), r.clone()]);
    let bv_result = tm.mk_term(bv_kind, &[l_bv, r_bv]);
    let result = match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul => {
            tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), bv_result])
        }
        // Comparisons already produce a Boolean term — no rewrap.
        _ => bv_result,
    };
    Some(Ok(result))
}

// ── `if`/`.N` projection arms ─────────────────────────────────────────────────

pub(super) fn encode_if<'tm>(
    cond: &SemExpr,
    then_expr: &SemExpr,
    else_expr: &SemExpr,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
    coerce_to: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    let c = encode_expr(cond, env, ctx, path_cond.clone(), None)?;

    // `elaborate_expr`'s `If` case rejects any condition whose Kind isn't
    // Bool, and sort-aware SSA constants mean a Kind::Bool value always
    // encodes to boolean sort — so `c` reaching here as non-boolean would
    // mean a Bool/Int value got silently conflated somewhere upstream.
    // Bool and Int are disjoint in Cantor's value model (feedback_bool_int_disjoint):
    // fail loudly instead of quietly coercing via `c != 0`.
    if !c.sort().is_boolean() {
        unreachable!(
            "encode_if: condition encoded to non-boolean sort {:?} — \
             elaborate_expr should have rejected a non-Bool if-condition",
            c.sort()
        );
    }
    let c_bool = c;

    // Then-branch: path_cond ∧ cond — propagate coerce_to so the branch
    // result is wrapped in the union datatype if needed.
    let then_guard = ctx
        .tm
        .mk_term(Kind::And, &[path_cond.clone(), c_bool.clone()]);
    let t = encode_expr(then_expr, env, ctx, then_guard, coerce_to.clone())?;

    // Else-branch: path_cond ∧ ¬cond
    let not_c = ctx.tm.mk_term(Kind::Not, std::slice::from_ref(&c_bool));
    let else_guard = ctx.tm.mk_term(Kind::And, &[path_cond.clone(), not_c]);
    let e = encode_expr(else_expr, env, ctx, else_guard, coerce_to.clone())?;

    // CVC5 requires both branches to have the same sort.
    // Unify sorts before calling mk_term(Ite, …).
    //
    // The common case where branches differ only because one is `fail`/
    // `fail n` (e.g. `if cond then 5 else fail` with range `Nat | Fail`) is
    // already handled above: `coerce_to` is propagated into both branches,
    // and each one's own `maybe_coerce` independently wraps it into the
    // enclosing union datatype (`Fail` is just another arm — see
    // docs/design-decisions.md §13), so `t.sort() == e.sort()` already holds
    // by the time we get here. There is no Fail-specific coercion left to do
    // in this function at all.
    let (t, e) = if t.sort() == e.sort() {
        (t, e)
    } else {
        // Branches have genuinely different sorts and cannot be unified —
        // Bool and Int are disjoint in Cantor's value model (no implicit
        // 0/1 coercion; write `if b then 1 else 0` to convert explicitly),
        // and anything else (distinct sort, tuple, future Float32, …) is no
        // more compatible. In practice `elaborate()` already rejects
        // mismatched non-Tuple/TaggedUnion branch Kinds for a legitimate
        // program (see `kind::merge_if_branches`), and any Fail-vs-success
        // mismatch should already have been unified via `coerce_to` above —
        // so reaching this arm at all means either an elaborator gap or a
        // missing `coerce_to` (e.g. a `let`/`:=` RHS, which doesn't thread
        // one through today). This is a defensive fallback, not a supported
        // path: for whichever branch isn't integer-sorted, push a
        // path-conditioned `false` obligation (that branch's value can never
        // satisfy an integer-shaped range) and substitute a dummy integer so
        // `Ite` stays well-sorted — a sound under-approximation, never a
        // silent pass.
        let tm = ctx.tm;
        let mut to_int_or_dummy = |b: Term<'tm>, path: Term<'tm>| {
            if b.sort().is_integer() {
                b
            } else {
                ctx.builtin_obligs.push(BuiltinObligation {
                    path_cond: path,
                    obligation: tm.mk_boolean(false),
                    violated_reason: "branch value's set cannot satisfy the range".to_string(),
                });
                tm.mk_integer(0)
            }
        };
        let not_c = tm.mk_term(Kind::Not, std::slice::from_ref(&c_bool));
        let then_path = tm.mk_term(Kind::And, &[path_cond.clone(), c_bool.clone()]);
        let else_path = tm.mk_term(Kind::And, &[path_cond.clone(), not_c]);
        (to_int_or_dummy(t, then_path), to_int_or_dummy(e, else_path))
    };

    Ok(ctx.tm.mk_term(Kind::Ite, &[c_bool, t, e]))
}

pub(super) fn encode_proj<'tm>(
    base: &SemExpr,
    index: usize,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
) -> Result<Term<'tm>, String> {
    let base_term = encode_expr(base, env, ctx, path_cond.clone(), None)?;

    // Struct vector indexing: `xs.N` / `xs[N]` on a sequence-sorted term.
    // (e.g. `(Nat * Nat)*` encoded as `Seq(Tuple(Int, Int))`).
    // Encode as SeqNth(xs, N) and push a bounds obligation (N < len(xs)).
    // The result has the element sort (e.g. Tuple(Int, Int)); the caller's
    // outer Proj, if any, lands on a tuple-sorted term that ApplySelector handles.
    if base_term.sort().is_sequence() {
        let idx_term = ctx.tm.mk_integer(index as i64);
        let nth = ctx
            .tm
            .mk_term(Kind::SeqNth, &[base_term.clone(), idx_term.clone()]);
        let len = ctx.tm.mk_term(Kind::SeqLength, &[base_term]);
        let in_bounds = ctx.tm.mk_term(Kind::Lt, &[idx_term, len]);
        ctx.builtin_obligs.push(BuiltinObligation {
            path_cond: path_cond.clone(),
            obligation: in_bounds,
            violated_reason: format!("vector index {index} may be out of bounds"),
        });
        return Ok(nth);
    }

    // CVC5 tuple sorts also satisfy is_dt() == true; we only want the
    // special-case path for cross-kind union DTs (non-tuple algebraic
    // datatypes built by build_union_datatype_sort).
    if base_term.sort().is_dt() && !base_term.sort().is_tuple() {
        // Find a tuple arm (constructor names start with "ck_T_") that has
        // enough fields for this projection index.
        let dt = base_term.sort().datatype();
        let tuple_ctor = (0..dt.num_constructors())
            .map(|i| dt.constructor(i))
            .find(|c| c.name().starts_with("ck_T_") && c.num_selectors() > index);

        return if let Some(ctor) = tuple_ctor {
            // Push a tester obligation: the value must be in the tuple arm.
            // If the solver finds a valuation where it is in the scalar arm,
            // it reports a counterexample.
            let tester = ctx
                .tm
                .mk_term(Kind::ApplyTester, &[ctor.tester_term(), base_term.clone()]);
            ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: tester,
                violated_reason: format!(
                    "projection `.{}` requires the value to be in the tuple arm; \
                     the scalar arm of the union would make this invalid",
                    index
                ),
            });
            // ApplySelector is arithmetic-safe (unlike TupleProject) and
            // works on symbolic DT terms, including Ite results.
            let sel = ctor.selector(index);
            Ok(ctx
                .tm
                .mk_term(Kind::ApplySelector, &[sel.term(), base_term]))
        } else {
            // No tuple arm with enough fields: projection is always invalid.
            ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: ctx.tm.mk_boolean(false),
                violated_reason: format!(
                    "projection `.{}` on a cross-kind union with no matching tuple arm",
                    index
                ),
            });
            Ok(ctx.tm.mk_integer(0))
        };
    }

    proj_from_tuple(ctx.tm, base_term, index)
}
