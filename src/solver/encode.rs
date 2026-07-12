//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, UnOp},
    semantics::tree::{SemExpr, SemExprKind, SemFunctionDef, flatten_cartesian_product},
    span::{Span, Symbol},
};

use super::NameDefs;
use super::encode_call::{CallSite, encode_call};
use super::encode_ctrl::{encode_if, encode_proj, encode_wrapping_binop, wrapping_info_for_sort};
use super::membership::{Membership, SolverPreds, membership_constraint};
use super::obligations::{
    BuiltinObligation, OverflowObligation, OverloadCallObligation, binary_builtin_domain,
    named_set, unary_builtin_domain,
};
use super::sort::{maybe_coerce, set_sort};

// ── Environment ───────────────────────────────────────────────────────────────

/// Map from variable name to its current SSA cvc5 term.
pub(crate) type Env<'tm> = HashMap<Symbol, Term<'tm>>;

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
    pub(crate) distinct_preds: &'a SolverPreds<'tm>,
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
            // Signed32/Unsigned32 (docs/wrapping-and-quotient-sets-plan.md):
            // `from(x)` unwraps via `from_D` (D_sort -> BitVec) then the
            // signed/unsigned BitVec->Int reading. Total, like the
            // constructor — no basis obligation.
            for info in ctx.distinct_preds.wrapping.values() {
                if arg_term.sort() == info.d_sort {
                    let bv = ctx
                        .tm
                        .mk_term(Kind::ApplyUf, &[info.from.clone(), arg_term]);
                    let to_int_kind = if info.signed {
                        Kind::BitvectorSbvToInt
                    } else {
                        Kind::BitvectorUbvToInt
                    };
                    return Ok(ctx.tm.mk_term(to_int_kind, &[bv]));
                }
            }
            for (sym, info) in ctx.distinct_preds.iter() {
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

        // `'c'` — always a valid Unicode scalar value by construction (Rust's
        // `char` excludes surrogates), so unlike `char(n)` this needs no
        // `unicode_scalar_valid` basis obligation — just apply `mk_Char`
        // directly and assert the same `from(mk_Char(n)) == n` round-trip
        // fact `char(n)` gets, so e.g. `from('A') == 65` stays provable.
        SemExprKind::CharLit(c) => {
            let info = ctx
                .distinct_preds
                .get(&Symbol::new("Char"))
                .expect("Char must be registered as a builtin distinct sort");
            let n = ctx.tm.mk_integer(*c as u32 as i64);
            let result = ctx.tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), n.clone()]);
            super::encode_call::assert_distinct_round_trip(ctx.tm, ctx.solver, info, &result, &n);
            Ok(result)
        }

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
    // Signed32/Unsigned32: `bvneg` wraps by construction (definitional, not
    // a proof obligation) — see the Add/Sub/Mul reasoning above
    // `encode_wrapping_binop`. Checked *before* `unary_builtin_domain`'s
    // "operand must be Int" obligation below, which would otherwise wrongly
    // reject every wrapping-sort negation as a domain violation (a wrapping
    // value is never a member of plain `Int`, by design — that obligation
    // is only meaningful for the ordinary `Int`-typed path).
    if matches!(op, UnOp::Neg)
        && let Some(info) = wrapping_info_for_sort(ctx.distinct_preds, &t.sort())
    {
        let bv = ctx.tm.mk_term(Kind::ApplyUf, &[info.from.clone(), t]);
        let neg = ctx.tm.mk_term(Kind::BitvectorNeg, &[bv]);
        return Ok(ctx.tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), neg]));
    }
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
///
/// `target_seq_sort`: the full `Seq(elem)` sort this term is meant to have,
/// when known from context (e.g. a `let`/`mut` binding's declared `X*`
/// constraint). Used two ways: as the element sort for an empty-tuple (`[]`)
/// term (which carries no sort information of its own), and — for a *nested*
/// vector like `Nat**` — to recursively coerce each element (itself a tuple
/// from an inner array literal like `[1, 2]`) into a real sequence too,
/// rather than wrapping a still-tuple-sorted element straight in `SeqUnit`
/// (which produces a `Seq` whose elements have mismatched sorts and aborts
/// cvc5 with "expecting comparable terms in concat"). Falls back to integer
/// element sort / no recursive coercion when `None` (the `++`-only call sites
/// don't have a declared target sort to hand).
pub(crate) fn coerce_to_sequence<'tm>(
    tm: &'tm TermManager,
    term: Term<'tm>,
    target_seq_sort: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    if term.sort().is_sequence() {
        return Ok(term);
    }
    if term.sort().is_tuple() {
        let dt = term.sort().datatype();
        let n_elems = dt.constructor(0).num_selectors();
        let elem_sort = target_seq_sort.map(|s| s.sequence_element_sort());
        if n_elems == 0 {
            // Empty tuple [] → empty sequence, in the caller-supplied element
            // sort if known, else integer as a last-resort fallback.
            return Ok(tm.mk_empty_sequence(elem_sort.unwrap_or_else(|| tm.integer_sort())));
        }
        // Non-empty: fold SeqUnit(elem_i) with SeqConcat. Each element is
        // recursively coerced first when the declared element sort is itself
        // a sequence sort (nested vector) and the element is still tuple-sorted.
        let coerce_elem = |field: Term<'tm>| -> Result<Term<'tm>, String> {
            match &elem_sort {
                Some(es) if es.is_sequence() && field.sort().is_tuple() => {
                    coerce_to_sequence(tm, field, Some(es.clone()))
                }
                _ => Ok(field),
            }
        };
        let ctor = dt.constructor(0);
        let first_sel = ctor.selector(0);
        let first_elem = tm.mk_term(Kind::ApplySelector, &[first_sel.term(), term.clone()]);
        let first_elem = coerce_elem(first_elem)?;
        let mut seq = tm.mk_term(Kind::SeqUnit, &[first_elem]);
        for i in 1..n_elems {
            let sel = ctor.selector(i);
            let elem = tm.mk_term(Kind::ApplySelector, &[sel.term(), term.clone()]);
            let elem = coerce_elem(elem)?;
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

    // Signed32/Unsigned32: `+ - *` and ordered comparisons route through
    // `bv*` operators instead of the generic Int-sorted path below — checked
    // *before* `binary_builtin_domain`'s "operand must be Int" obligation,
    // which would otherwise wrongly reject every wrapping-sort arithmetic
    // expression as a domain violation (a wrapping value is never a member
    // of plain `Int`, by design — that obligation is only meaningful for
    // the ordinary `Int`-typed path). `==`/`!=` deliberately fall through
    // unchanged (plain CVC5 term equality on matching sorts is already
    // correct with no wrapping-specific code — see the module comment above
    // `encode_wrapping_binop`).
    if let Some(result) = encode_wrapping_binop(op, &l, &r, ctx) {
        return result;
    }

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
        let l_seq = coerce_to_sequence(ctx.tm, l.clone(), None)?;
        let r_seq = coerce_to_sequence(ctx.tm, r.clone(), None)?;
        return Ok(ctx.tm.mk_term(Kind::SeqConcat, &[l_seq, r_seq]));
    }

    let kind = match op {
        BinOp::Add => Kind::Add,
        BinOp::Sub => Kind::Sub,
        BinOp::Mul => Kind::Mult,
        BinOp::Div => Kind::IntsDivision,
        // Euclidean by design (fork 2 of docs/wrapping-and-quotient-sets-plan.md):
        // cvc5's `IntsDivision`/`IntsModulus` (SMT-LIB `div`/`mod`) are already
        // Euclidean, so `quot`/`rem` map onto them directly with no correction —
        // unlike `/`, which is *documented* truncating but *encoded* Euclidean
        // (the long-standing, deliberately-deferred mismatch noted above).
        BinOp::Quot => Kind::IntsDivision,
        BinOp::Rem => Kind::IntsModulus,
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
            | BinOp::Rem
            | BinOp::Quot
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
    // TODO: `Kind::IntsDivision` is SMT-LIB's Euclidean `div` (remainder
    // always non-negative), while codegen's `sdiv` truncates toward zero
    // (matching docs/design-decisions.md's *current* stated `/` semantics).
    // These disagree for negative operands. Confirmed 2026-07-05: this is a
    // rapid-prototyping-era placeholder, not a bug to reconcile in place —
    // `/` is intended to eventually produce `Rational` (a future numeric-
    // tower addition, see docs/wrapping-and-quotient-sets-plan.md), at which
    // point today's Int-truncating `/` goes away entirely and is replaced by
    // dedicated `tdiv`/`trem` truncating-division operators (low priority,
    // separate from the Euclidean `quot`/`rem` pair that plan introduces).
    // Leave this mismatch as-is until then rather than patching it piecemeal.
    //
    // `Quot` shares `/`'s exact overflow corner (`i64::MIN quot -1` is the
    // one case that doesn't fit in Int64) so it gets the same obligation.
    // `Rem` needs none: a Euclidean remainder is always `0 <= rem < |divisor|`,
    // strictly bounded by an already-Int64 divisor, so it can never overflow —
    // proving this needlessly would just cost a solver call for a fact that's
    // true by construction.
    if matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Quot
    ) && let Membership::Constrained(c) = membership_constraint(
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
    distinct_preds: &SolverPreds<'tm>,
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
