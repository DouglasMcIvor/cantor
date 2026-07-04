//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, UnOp},
    semantics::tree::{SemExpr, SemExprKind, SemFunctionDef, flatten_cartesian_product},
    span::{Span, Symbol},
};

use super::blocks::check_require;
use super::encode_call::{CallSite, encode_call};
use super::membership::{DistinctPreds, Membership, membership_constraint};
use super::sort::{maybe_coerce, set_sort};
use super::{CheckResult, NameDefs};

// ── Environment ───────────────────────────────────────────────────────────────

/// Map from variable name to its current SSA cvc5 term.
pub(crate) type Env<'tm> = HashMap<Symbol, Term<'tm>>;

// ── Built-in operator domain table ───────────────────────────────────────────

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

/// Everything `encode_expr` and its arm helpers (`encode_unop`/`encode_binop`/
/// `encode_if`/`encode_proj`/`encode_call`) thread unchanged through the whole
/// recursive descent over one function body. `env` is deliberately *not* a
/// field here: it gains new bindings inside nested scopes (`let`, block
/// params), so it stays a separate argument alongside whichever `SemExpr`
/// and `path_cond`/`coerce_to` are specific to one call.
pub(crate) struct EncodeCtx<'a, 'tm> {
    pub(crate) name_defs: &'a NameDefs,
    pub(crate) fn_env: &'a HashMap<Symbol, Vec<&'a SemFunctionDef>>,
    pub(crate) tm: &'tm TermManager,
    pub(crate) solver: &'a mut Solver<'tm>,
    pub(crate) call_counter: &'a mut usize,
    pub(crate) builtin_obligs: &'a mut Vec<BuiltinObligation<'tm>>,
    pub(crate) overflow_obligs: &'a mut Vec<OverflowObligation<'tm>>,
    pub(crate) overload_obligs: &'a mut Vec<OverloadCallObligation<'tm>>,
    pub(crate) distinct_preds: &'a DistinctPreds<'tm>,
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
            check_require(implication, tm, solver, &[], &[]),
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
                check_require(implication, tm, solver, &[], &[]),
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

// ── Expression encoder (compact router) ──────────────────────────────────────

/// Recursively encode a Cantor expression as a cvc5 `Term`.
///
/// When a function call is encountered, a fresh integer variable is introduced
/// for the return value, and the callee's per-signature contracts are asserted
/// as implications: `args ∈ domain → result ∈ range`.
///
/// `path_cond` is the conjunction of all branch conditions required to reach
/// this point in the expression.  `builtin_obligs` accumulates one entry per
/// built-in operator argument that has a domain constraint; the caller then
/// asserts `path_cond → obligation` for each, giving path-sensitive checking.
///
/// `coerce_to`: when `Some(sort)`, coerce integer/boolean/tuple-sorted results
/// to that union datatype sort.  Used to unify cross-kind union if/else branches
/// so both arms have the same CVC5 sort before `Ite` is applied.
pub(crate) fn encode_expr<'tm>(
    expr: &SemExpr,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
    coerce_to: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, ctx, path_cond.clone(), None)
        };
    }

    // `size()`, `from()`, and `len()` are built-in call builtins that bypass the
    // final maybe_coerce (they return predicates / unwrapped scalars, not union values).
    if let SemExprKind::Call { callee, args } = &expr.kind {
        // `len(xs)` — the number of elements in a vector (X* value).
        // Encoded as `seq.len(xs)` in the cvc5 sequence theory.
        if callee.0 == "len" && args.len() == 1 {
            let arg_term = enc!(&args[0])?;
            if !arg_term.sort().is_sequence() {
                return Err("len() expects a vector (X*) argument; \
                     use it only on Kleene-star values"
                    .into());
            }
            return Ok(ctx.tm.mk_term(Kind::SeqLength, &[arg_term]));
        }
        if callee.0 == "size" && args.len() == 1 {
            let fresh = format!("_size_{}", *ctx.call_counter);
            *ctx.call_counter += 1;
            let result = ctx.tm.mk_const(ctx.tm.integer_sort(), &fresh);
            let non_neg = ctx
                .tm
                .mk_term(Kind::Geq, &[result.clone(), ctx.tm.mk_integer(0)]);
            ctx.solver.assert_formula(non_neg);
            return Ok(result);
        }
        if callee.0 == "from" && args.len() == 1 {
            let arg_term = enc!(&args[0])?;
            for (sym, info) in ctx.distinct_preds {
                // `Fail` is registered as a distinct sort purely so the
                // cross-kind union machinery treats it like any other arm —
                // it has no user-facing basis value to extract, so `from()`
                // (which unwraps a real `distinct B` back to its `B` basis)
                // must not match it.
                if sym.0 == "Fail" {
                    continue;
                }
                if arg_term.sort() == info.sort {
                    let result = ctx
                        .tm
                        .mk_term(Kind::ApplyUf, &[info.from.clone(), arg_term]);
                    if let Some(def) = ctx.name_defs.get(sym)
                        && let Membership::Constrained(c) = membership_constraint(
                            ctx.tm,
                            result.clone(),
                            &def.value,
                            ctx.name_defs,
                            ctx.distinct_preds,
                        )
                    {
                        ctx.solver.assert_formula(c);
                    }
                    return Ok(result);
                }
            }
            return Err(
                "from() applied to a value that is not a member of any distinct set".into(),
            );
        }
    }

    let term = match &expr.kind {
        SemExprKind::IntLit(n) => Ok(ctx.tm.mk_integer(*n)),
        SemExprKind::BoolLit(b) => Ok(ctx.tm.mk_boolean(*b)),

        // `Fail` is a builtin distinct sort (registered in `build_distinct_preds`)
        // with one canonical witness value — the witness is never observed (see
        // the `from()` guard below), so any fixed integer works. `fail` applies
        // the `mk_Fail` constructor directly; `fail expr` pairs it with the
        // payload as a genuine tuple, exactly like any other cross-kind union's
        // payload-carrying arm. The surrounding `coerce_to`/`maybe_coerce`
        // machinery (end of this function) then wraps either shape into the
        // enclosing union datatype with no Fail-specific coercion code at all.
        SemExprKind::FailLit => {
            let info = ctx
                .distinct_preds
                .get(&Symbol::new("Fail"))
                .expect("Fail must be registered as a builtin distinct sort");
            Ok(ctx
                .tm
                .mk_term(Kind::ApplyUf, &[info.mk.clone(), ctx.tm.mk_integer(0)]))
        }

        SemExprKind::FailWith(inner) => {
            let n = enc!(inner)?;
            let info = ctx
                .distinct_preds
                .get(&Symbol::new("Fail"))
                .expect("Fail must be registered as a builtin distinct sort");
            let tag = ctx
                .tm
                .mk_term(Kind::ApplyUf, &[info.mk.clone(), ctx.tm.mk_integer(0)]);
            Ok(ctx.tm.mk_tuple(&[tag, n]))
        }

        SemExprKind::Var(sym) => {
            if let Some(term) = env.get(sym) {
                Ok(term.clone())
            } else if let Some(def) = ctx.name_defs.get(sym) {
                let def_value = def.value.clone();
                encode_expr(&def_value, &Env::new(), ctx, path_cond.clone(), None)
            } else {
                Err(format!("unbound variable `{}`", sym.0))
            }
        }

        SemExprKind::Tuple(elems) => {
            let terms = elems
                .iter()
                .map(|e| enc!(e))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ctx.tm.mk_tuple(&terms))
        }

        SemExprKind::UnOp { op, expr: inner } => {
            encode_unop(op, inner, expr.span, env, ctx, path_cond.clone())
        }

        // `+ - * /` are dedicated SemExprKind variants (never wrapped in
        // BinOp — see tree.rs's module doc); route them through the same
        // `encode_binop` that handles the remaining operators, so the
        // domain-obligation logic (Int-only, non-zero divisor, …) isn't
        // duplicated between an arithmetic-only path and the generic one.
        SemExprKind::Add(lhs, rhs) => encode_binop(
            &BinOp::Add,
            lhs,
            rhs,
            expr.span,
            env,
            ctx,
            path_cond.clone(),
        ),
        SemExprKind::Sub(lhs, rhs) => encode_binop(
            &BinOp::Sub,
            lhs,
            rhs,
            expr.span,
            env,
            ctx,
            path_cond.clone(),
        ),
        SemExprKind::Mul(lhs, rhs) => encode_binop(
            &BinOp::Mul,
            lhs,
            rhs,
            expr.span,
            env,
            ctx,
            path_cond.clone(),
        ),
        SemExprKind::Div(lhs, rhs) => encode_binop(
            &BinOp::Div,
            lhs,
            rhs,
            expr.span,
            env,
            ctx,
            path_cond.clone(),
        ),

        SemExprKind::BinOp { op, lhs, rhs } => {
            encode_binop(op, lhs, rhs, expr.span, env, ctx, path_cond.clone())
        }

        SemExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => encode_if(
            cond,
            then_expr,
            else_expr,
            env,
            ctx,
            path_cond.clone(),
            coerce_to.clone(),
        ),

        SemExprKind::Call { callee, args } => encode_call(
            &CallSite {
                callee,
                args,
                span: expr.span,
            },
            env,
            ctx,
            path_cond.clone(),
            coerce_to.clone(),
            false,
        ),

        // `f(args)?` — on the success path the result lies in the success arm
        // of the callee's range. That narrowing is only valid for a signature
        // whose domain the arguments actually satisfy, so it is asserted
        // per-signature as `args ∈ domain_i → result ∈ success_arm(range_i)`
        // inside `encode_call` (`narrow_try`), never unconditionally — an
        // unguarded assertion would let an out-of-domain or other-overload
        // call "prove" the wrong success set.
        SemExprKind::Try(inner) => match &inner.kind {
            SemExprKind::Call { callee, args } => encode_call(
                &CallSite {
                    callee,
                    args,
                    span: inner.span,
                },
                env,
                ctx,
                path_cond.clone(),
                None,
                true,
            ),
            _ => enc!(inner),
        },

        SemExprKind::Proj { base, index } => encode_proj(base, *index, env, ctx, path_cond.clone()),

        SemExprKind::Index { base, index } => {
            let base_term = enc!(base)?;
            let idx_term = enc!(index)?;
            if !base_term.sort().is_sequence() {
                return Err("runtime index `xs[i]` is only valid on vector (X*) values".into());
            }
            // Push a bounds obligation for all vector indexing: the solver tracks
            // whether `0 ≤ i < len(xs)` is provable.  Scalar element sorts (Int /
            // Bool) have benign out-of-bounds defaults (0 / false), so this is
            // technically optional for them but keeps the model correct.  For tuple
            // element sorts (struct vecs) it is essential: CVC5 can assign arbitrary
            // default components that fall outside the element range, producing false
            // counterexamples without this obligation.
            let len = ctx
                .tm
                .mk_term(Kind::SeqLength, std::slice::from_ref(&base_term));
            let lo = ctx
                .tm
                .mk_term(Kind::Leq, &[ctx.tm.mk_integer(0), idx_term.clone()]);
            let hi = ctx.tm.mk_term(Kind::Lt, &[idx_term.clone(), len]);
            ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: ctx.tm.mk_term(Kind::And, &[lo, hi]),
                violated_reason: "vector index may be out of bounds".into(),
            });
            Ok(ctx.tm.mk_term(Kind::SeqNth, &[base_term, idx_term]))
        }

        SemExprKind::SetLit(_) | SemExprKind::Comprehension { .. } | SemExprKind::KleeneStar(_) => {
            Err("set expressions cannot appear in value position \
                 (only in domain/range/`in`/`for` positions)"
                .into())
        }

        // Set-position-only variants: elaboration never threads these into a
        // value-position tree (see `semantics::elaborate`'s module doc), so
        // reaching them here means an elaborator invariant broke.
        SemExprKind::DisjointUnion(..)
        | SemExprKind::SetDifference(..)
        | SemExprKind::CartesianProduct(..)
        | SemExprKind::SetQuotient(..) => Err(format!(
            "elaborator invariant broken: set-position node {:?} reached encode_expr \
                 (value position)",
            expr.kind
        )),
    }?;

    maybe_coerce(ctx.tm, term, &coerce_to)
}

// ── Arm helpers ───────────────────────────────────────────────────────────────

fn encode_unop<'tm>(
    op: &UnOp,
    inner: &SemExpr,
    span: Span,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
) -> Result<Term<'tm>, String> {
    let t = encode_expr(inner, env, ctx, path_cond.clone(), None)?;
    for (domain, reason) in unary_builtin_domain(op) {
        if let Membership::Constrained(c) = membership_constraint(
            ctx.tm,
            t.clone(),
            &domain,
            ctx.name_defs,
            ctx.distinct_preds,
        ) {
            ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: c,
                violated_reason: reason.to_string(),
            });
        }
    }
    match op {
        UnOp::Neg => {
            // Guard: wrong-sort operand (e.g. distinct-sort) — domain check
            // pushed Constrained(false); return dummy to avoid CVC5 sort panic.
            if !t.sort().is_integer() {
                return Ok(ctx.tm.mk_integer(0));
            }
            let result = ctx.tm.mk_term(Kind::Neg, &[t]);
            // int-soundness-plan phase 1: `-x` overflows only at `i64::MIN`.
            // Checked/elided by codegen based on whether this holds, keyed by span.
            if let Membership::Constrained(c) = membership_constraint(
                ctx.tm,
                result.clone(),
                &named_set("Int64"),
                ctx.name_defs,
                ctx.distinct_preds,
            ) {
                ctx.overflow_obligs.push(OverflowObligation {
                    span,
                    path_cond: path_cond.clone(),
                    obligation: c,
                });
            }
            Ok(result)
        }
        UnOp::Not => {
            // Guard: wrong-sort operand — domain check pushed Constrained(false);
            // return dummy to avoid CVC5 sort panic.
            if !t.sort().is_boolean() {
                return Ok(ctx.tm.mk_boolean(false));
            }
            Ok(ctx.tm.mk_term(Kind::Not, &[t]))
        }
    }
}

/// Coerce a cvc5 term to sequence sort for use with `SeqConcat`.
///
/// If `term` is already sequence-sorted, return it unchanged.
/// If `term` is tuple-sorted (from an array literal like `[1, 2, 3]`),
/// convert it by wrapping each element in `SeqUnit` and concatenating.
/// Otherwise return an error: `++` only works on vector (X*) values.
fn coerce_to_sequence<'tm>(tm: &'tm TermManager, term: Term<'tm>) -> Result<Term<'tm>, String> {
    if term.sort().is_sequence() {
        return Ok(term);
    }
    if term.sort().is_tuple() {
        let dt = term.sort().datatype();
        let n_elems = dt.constructor(0).num_selectors();
        if n_elems == 0 {
            // Empty tuple [] → empty sequence.  Element sort must be inferred from
            // context; we use integer as the fallback since `[]` only makes sense
            // for a known element-sort vector — the solver will constrain further.
            return Ok(tm.mk_empty_sequence(tm.integer_sort()));
        }
        // Non-empty: fold SeqUnit(elem_i) with SeqConcat.
        let ctor = dt.constructor(0);
        let first_sel = ctor.selector(0);
        let first_elem = tm.mk_term(Kind::ApplySelector, &[first_sel.term(), term.clone()]);
        let mut seq = tm.mk_term(Kind::SeqUnit, &[first_elem]);
        for i in 1..n_elems {
            let sel = ctor.selector(i);
            let elem = tm.mk_term(Kind::ApplySelector, &[sel.term(), term.clone()]);
            let unit = tm.mk_term(Kind::SeqUnit, &[elem]);
            seq = tm.mk_term(Kind::SeqConcat, &[seq, unit]);
        }
        return Ok(seq);
    }
    Err("`++` requires vector (X*) operands; operand is not a sequence or array literal".into())
}

fn encode_binop<'tm>(
    op: &BinOp,
    lhs: &SemExpr,
    rhs: &SemExpr,
    span: Span,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, ctx, path_cond.clone(), None)
        };
    }

    // `x in S` and `x not in S` are boolean membership predicates.
    // Handle them before encoding both sides, since the RHS is a set
    // expression (not an integer term) and would fail normal encoding.
    match op {
        BinOp::In => {
            // If the set RHS is a variable bound in the solver env it's a
            // runtime set value — membership can't be decided at proof time.
            if let SemExprKind::Var(sym) = &rhs.kind
                && env.contains_key(sym)
            {
                let fresh = format!("_in_{}", *ctx.call_counter);
                *ctx.call_counter += 1;
                return Ok(ctx.tm.mk_const(ctx.tm.boolean_sort(), &fresh));
            }
            let l = enc!(lhs)?;
            return match membership_constraint(ctx.tm, l, rhs, ctx.name_defs, ctx.distinct_preds) {
                Membership::Constrained(c) => Ok(c),
                Membership::Unconstrained => Ok(ctx.tm.mk_boolean(true)),
                Membership::Unsupported => Err("unsupported set in `in` expression".into()),
            };
        }
        BinOp::NotIn => {
            if let SemExprKind::Var(sym) = &rhs.kind
                && env.contains_key(sym)
            {
                let fresh = format!("_in_{}", *ctx.call_counter);
                *ctx.call_counter += 1;
                let b = ctx.tm.mk_const(ctx.tm.boolean_sort(), &fresh);
                return Ok(ctx.tm.mk_term(Kind::Not, &[b]));
            }
            let l = enc!(lhs)?;
            return match membership_constraint(ctx.tm, l, rhs, ctx.name_defs, ctx.distinct_preds) {
                Membership::Constrained(c) => Ok(ctx.tm.mk_term(Kind::Not, &[c])),
                Membership::Unconstrained => Ok(ctx.tm.mk_boolean(false)),
                Membership::Unsupported => Err("unsupported set in `not in` expression".into()),
            };
        }
        _ => {}
    }

    let l = enc!(lhs)?;
    let r = enc!(rhs)?;

    for (arg_idx, arg_term) in [&l, &r].iter().enumerate() {
        for (domain, reason) in binary_builtin_domain(op, arg_idx) {
            if let Membership::Constrained(c) = membership_constraint(
                ctx.tm,
                (*arg_term).clone(),
                &domain,
                ctx.name_defs,
                ctx.distinct_preds,
            ) {
                ctx.builtin_obligs.push(BuiltinObligation {
                    path_cond: path_cond.clone(),
                    obligation: c,
                    violated_reason: reason.to_string(),
                });
            }
        }
    }

    // `xs ++ ys` — vector concatenation.  Both operands must be sequence-sorted.
    // If either is a tuple (from an array literal), coerce it to a sequence first.
    if *op == BinOp::Concat {
        let l_seq = coerce_to_sequence(ctx.tm, l.clone())?;
        let r_seq = coerce_to_sequence(ctx.tm, r.clone())?;
        return Ok(ctx.tm.mk_term(Kind::SeqConcat, &[l_seq, r_seq]));
    }

    let kind = match op {
        BinOp::Add => Kind::Add,
        BinOp::Sub => Kind::Sub,
        BinOp::Mul => Kind::Mult,
        BinOp::Div => Kind::IntsDivision,
        BinOp::Eq => Kind::Equal,
        BinOp::Ne => Kind::Distinct,
        BinOp::Lt => Kind::Lt,
        BinOp::Le => Kind::Leq,
        BinOp::Gt => Kind::Gt,
        BinOp::Ge => Kind::Geq,
        BinOp::And => Kind::And,
        BinOp::Or => Kind::Or,
        BinOp::In | BinOp::NotIn => unreachable!("handled above"),
        BinOp::Concat => unreachable!("handled above"),
        BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
            return Err(format!("set operation `{op:?}` not yet encodable"));
        }
    };

    // `==`/`!=` between different solver sorts would be an ill-sorted CVC5
    // term (process abort). Elaboration already rejects cross-kind operands;
    // what reaches here is same-Kind-different-sort — e.g. a distinct-set
    // value against its basis (`litre(3) == 3`), where the honest answer is
    // Unknown until distinct equality is modelled explicitly.
    if matches!(op, BinOp::Eq | BinOp::Ne) && l.sort() != r.sort() {
        return Err(format!(
            "cannot encode `{op:?}` between values with different solver \
             representations (e.g. a distinct-set value and its basis) — \
             unwrap with from() first"
        ));
    }

    // Guard: bail out with a sort-safe dummy when operands have the wrong sort.
    // The domain checks above push Constrained(false) obligations that cause
    // a counterexample; the dummy prevents a CVC5 sort panic.
    if matches!(
        op,
        BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
    ) && (!l.sort().is_integer() || !r.sort().is_integer())
    {
        return Ok(ctx.tm.mk_integer(0));
    }
    if matches!(op, BinOp::And | BinOp::Or) && (!l.sort().is_boolean() || !r.sort().is_boolean()) {
        return Ok(ctx.tm.mk_boolean(false));
    }

    let result = ctx.tm.mk_term(kind, &[l, r]);

    // int-soundness-plan phase 1: `+ - * /` all carry an implicit "result fits
    // in Int64" obligation. For `/` this is mathematically only ever violated
    // by `i64::MIN / -1` (the divisor-nonzero obligation above is unrelated
    // and stays a hard proof gate) — the uniform `∈ Int64` framing captures
    // that case too, and lets codegen (which knows operands are already
    // runtime-valid i64 words) pick a cheaper guard than a general overflow
    // intrinsic for `/` specifically.
    //
    // TODO(int-soundness-plan): `Kind::IntsDivision` is SMT-LIB's Euclidean
    // `div` (remainder always non-negative), while codegen's `sdiv` truncates
    // toward zero (matching docs/design-decisions.md's stated `/` semantics).
    // These disagree for negative operands — a separate, pre-existing gap
    // flagged during phase 1 but deliberately out of scope here.
    if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div)
        && let Membership::Constrained(c) = membership_constraint(
            ctx.tm,
            result.clone(),
            &named_set("Int64"),
            ctx.name_defs,
            ctx.distinct_preds,
        )
    {
        ctx.overflow_obligs.push(OverflowObligation {
            span,
            path_cond: path_cond.clone(),
            obligation: c,
        });
    }

    Ok(result)
}

fn encode_if<'tm>(
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

fn encode_proj<'tm>(
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

// ── Value extraction helpers ──────────────────────────────────────────────────

/// Extract an i64 from a cvc5 integer model term.
pub(crate) fn integer_value(term: &Term<'_>) -> i64 {
    if term.is_int32_value() {
        term.int32_value() as i64
    } else if term.is_int64_value() {
        term.int64_value()
    } else {
        term.to_string().trim().parse::<i64>().unwrap_or(0)
    }
}

/// Extract a bool from a cvc5 boolean model term.
pub(crate) fn boolean_value(term: &Term<'_>) -> bool {
    term.to_string().trim() == "true"
}

// ── Tuple projection helpers ──────────────────────────────────────────────────

/// Project field `index` from a tuple-sorted CVC5 term.
///
/// Uses `ApplySelector` rather than `child(index + 1)` so this works for any
/// tuple-sorted term: concrete `mk_tuple(a, b, c)` applications, `Ite` results,
/// and `SeqNth` results (which are symbolic, not `APPLY_CONSTRUCTOR` terms).
pub(crate) fn proj_from_tuple<'tm>(
    tm: &'tm TermManager,
    base: Term<'tm>,
    index: usize,
) -> Result<Term<'tm>, String> {
    let sel = base.sort().datatype().constructor(0).selector(index);
    Ok(tm.mk_term(Kind::ApplySelector, &[sel.term(), base]))
}

/// Number of elements in a tuple-sorted term, read from its sort's datatype —
/// works for any tuple-sorted term, not just genuine `mk_tuple(...)` constructor
/// applications (an opaque SSA constant carrying a tuple sort has no children,
/// but its sort still knows its own arity).
pub(crate) fn tuple_arity<'tm>(base: &Term<'tm>) -> usize {
    base.sort().datatype().constructor(0).num_selectors()
}

/// Create a decomposed representation of a tuple-valued term.
///
/// For a product set `A * B`, creates individual leaf scalar constants
/// and assembles them with `mk_tuple`. This avoids symbolic tuple-sorted
/// constants, which cvc5 rejects when used in arithmetic contexts via
/// `TupleProject` (beta-reduction only works on `mk_tuple(...)` terms).
///
/// Returns `(assembled_term, leaves)` where each leaf is `(leaf_term, leaf_set_expr)`.
/// The caller asserts membership for each leaf separately (scalars are arithmetic-safe).
pub(crate) fn mk_decomposed_tuple<'tm, 'e>(
    tm: &'tm TermManager,
    name: &str,
    set_expr: &'e SemExpr,
    distinct_preds: &DistinctPreds<'tm>,
    name_defs: &NameDefs,
) -> (Term<'tm>, Vec<(Term<'tm>, &'e SemExpr)>) {
    let parts = flatten_cartesian_product(set_expr);
    if parts.len() <= 1 {
        let sort = set_sort(tm, set_expr, distinct_preds, name_defs)
            .expect("mk_decomposed_tuple: leaf set expression has no representable CVC5 sort");
        let leaf = tm.mk_const(sort, name);
        return (leaf.clone(), vec![(leaf, set_expr)]);
    }
    let mut leaves = Vec::new();
    let mut child_terms = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        let child_name = format!("{name}__{i}");
        let (child_term, child_leaves) =
            mk_decomposed_tuple(tm, &child_name, part, distinct_preds, name_defs);
        leaves.extend(child_leaves);
        child_terms.push(child_term);
    }
    (tm.mk_tuple(&child_terms), leaves)
}
