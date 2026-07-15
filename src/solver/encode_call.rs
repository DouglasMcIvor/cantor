//! Call-site encoding and domain/contract obligations.
//!
//! Split out of `encode.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — this module holds the
//! call-related machinery (`encode_call` itself, the call-site domain
//! obligation, and callee-contract assertion), while `encode.rs` keeps the
//! expression router and its non-call arms.

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::DefKind,
    kind::Kind as ValKind,
    semantics::tree::{SemExpr, SemFunctionDef, SemFunctionSig, sem_param_set_exprs},
    span::{Span, Symbol},
};

use super::NameDefs;
use super::membership::{DistinctInfo, Membership, SolverPreds, membership_constraint};
use super::sort::{
    extract_success_value, is_product_range, maybe_coerce, set_sort, success_arm_of_range,
};

use super::encode::{EncodeCtx, Env, encode_expr, mk_decomposed_tuple};
use super::obligations::{BuiltinObligation, OverloadCallObligation};

// ── Call encoder ──────────────────────────────────────────────────────────────

/// The pieces of a `Call`/`Try(Call)` node `encode_call` needs from its
/// caller, bundled to keep the function under clippy's argument-count limit
/// — same fix as the `EncodeCtx`/`BlockCtx`/`LoopCtx` family (see project
/// history for the established pattern).
#[derive(Clone, Copy)]
pub(crate) struct CallSite<'e> {
    pub(crate) callee: &'e Symbol,
    pub(crate) args: &'e [SemExpr],
    pub(crate) span: Span,
}

pub(crate) fn encode_call<'tm>(
    call: &CallSite<'_>,
    env: &Env<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: Term<'tm>,
    coerce_to: Option<cvc5::Sort<'tm>>,
    // True when this call sits directly under `?`: additionally assert the
    // per-signature success-narrowing `args ∈ domain_i → result ∈ success_arm_i`.
    narrow_try: bool,
) -> Result<Term<'tm>, String> {
    let CallSite {
        callee,
        args,
        span: call_span,
    } = *call;
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, ctx, path_cond.clone(), None)
        };
    }

    // Auto-generated constructor: `litre(n)` for `Litre = distinct Nat`.
    // Detected by capitalising the first letter of callee and checking name_defs.
    // Apply the `mk` UF — result has sort D_sort (distinct sort).
    // Emit a basis obligation so `litre(x)` with x : Int is rejected when x ∉ Nat.
    if args.len() == 1
        && let Some(distinct_def) = distinct_def_for_constructor(callee, ctx.name_defs)
        && let Some(info) = ctx.distinct_preds.get(&distinct_def.name)
    {
        let arg_term = enc!(&args[0])?;
        match membership_constraint(
            ctx.tm,
            arg_term.clone(),
            &distinct_def.value,
            ctx.name_defs,
            ctx.distinct_preds,
        ) {
            Membership::Constrained(c) => ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: c,
                violated_reason: format!(
                    "argument to {}() must satisfy the basis constraint",
                    callee.0
                ),
            }),
            Membership::Unconstrained | Membership::Unsupported => {}
        }
        let result = ctx
            .tm
            .mk_term(Kind::ApplyUf, &[info.mk.clone(), arg_term.clone()]);
        assert_distinct_round_trip(ctx.tm, ctx.solver, info, &result, &arg_term);
        // maybe_coerce handles distinct→DT coercion; router's final call is a no-op.
        return maybe_coerce(ctx.tm, result, &coerce_to);
    }

    // Auto-generated constructor: `signed32(n)`/`unsigned32(n)`
    // (docs/wrapping-and-quotient-sets-plan.md). Total — every `Int` maps to
    // *some* bit pattern, so unlike `distinct` there's no basis obligation to
    // emit. `int2bv` handles the mod-2^32 reduction for arbitrary (including
    // negative, or >= 2^32) integers internally — confirmed against the real
    // cvc5 crate before writing this (see the plan doc's spike note).
    if args.len() == 1
        && let Some(info) = wrapping_info_for_constructor(callee, ctx.distinct_preds)
    {
        let arg_term = enc!(&args[0])?;
        let int2bv = ctx.tm.mk_op(Kind::IntToBitvector, &[info.width]);
        let bv = ctx.tm.mk_term_from_op(int2bv, &[arg_term]);
        let result = ctx.tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), bv]);
        return maybe_coerce(ctx.tm, result, &coerce_to);
    }

    // Auto-generated constructor: `char(n)` for the builtin `Char` distinct
    // sort (docs/design-decisions.md §13). Unlike Signed32/Unsigned32, not
    // every `Int` is a valid Unicode scalar — emit a basis obligation (like
    // `litre(n)` above) using the hardcoded `unicode_scalar_valid` predicate
    // instead of `membership_constraint` over a `NameDef` (Char has none).
    if args.len() == 1
        && let Some(info) = char_info_for_constructor(callee, ctx.distinct_preds)
    {
        let arg_term = enc!(&args[0])?;
        if let Membership::Constrained(c) =
            super::membership::unicode_scalar_valid(ctx.tm, arg_term.clone())
        {
            ctx.builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: c,
                violated_reason: "argument to char() must be a valid Unicode scalar value \
                     (0..=0x10FFFF, excluding surrogates 0xD800..=0xDFFF)"
                    .to_string(),
            });
        }
        let result = ctx
            .tm
            .mk_term(Kind::ApplyUf, &[info.mk.clone(), arg_term.clone()]);
        assert_distinct_round_trip(ctx.tm, ctx.solver, info, &result, &arg_term);
        return maybe_coerce(ctx.tm, result, &coerce_to);
    }

    let arg_terms: Vec<Term<'_>> = args.iter().map(|a| enc!(a)).collect::<Result<_, _>>()?;

    let overload_set = ctx
        .fn_env
        .get(callee)
        .ok_or_else(|| format!("unknown function `{}`", callee.0))?;

    // int-soundness-plan phase 2: only definitions whose arity matches this
    // call are candidates — arity alone is always statically decidable, so a
    // def of a different arity contributes nothing here (mirrors, at the
    // overload-set level, the per-signature `DomainMatch::Mismatch` arm
    // below). Indices are positions in the whole same-name `Vec`, matching
    // codegen's mangled-name table and `ConstrainedTree::overload_resolution`.
    let arity_matching: Vec<(usize, &SemFunctionDef)> = overload_set
        .iter()
        .enumerate()
        .filter(|(_, def)| def.params.len() == args.len())
        .map(|(i, def)| (i, *def))
        .collect();

    // backlog.md "function overloads — support different kinds": with more
    // than one arity-matching candidate, further filter to the ones whose
    // parameter-Kind bucket matches this call's *actual* argument Kinds
    // (already elaborated, always statically known) — otherwise a
    // Kind-heterogeneous overload set (e.g. `f : Bool -> Bool` alongside
    // `f : Nat -> Nat`) would let a mismatched-sort candidate reach
    // `membership_constraint` below and build a nonsensical cross-sort SMT
    // term. Skipped entirely when there's at most one arity-matching
    // candidate — that's the single-signature common case, where the
    // argument may legitimately *coerce* into the declared param Kind
    // (e.g. sequence-unification's scalar-to-`Vector` boxing) without an
    // exact match, and there is nothing to disambiguate anyway. Falls back
    // to `arity_matching` unfiltered if nothing matches by Kind — should
    // never happen for a tree that passed elaboration (which already
    // guarantees some bucket matches), but this stays a soft fallback
    // rather than a hard error since this module reports failures as
    // `Unknown`/counterexamples, not compiler panics.
    let candidates: Vec<(usize, &SemFunctionDef)> = if arity_matching.len() <= 1 {
        arity_matching
    } else {
        let filtered: Vec<(usize, &SemFunctionDef)> = arity_matching
            .iter()
            .filter(|(_, def)| {
                def.param_kinds.len() == args.len()
                    && def.param_kinds.iter().zip(args).all(|(p, a)| {
                        crate::semantics::elaborate::canonical_bucket_kind(p)
                            == crate::semantics::elaborate::canonical_bucket_kind(&a.kind_of)
                    })
            })
            .copied()
            .collect();
        if filtered.is_empty() {
            arity_matching
        } else {
            filtered
        }
    };

    push_call_domain_obligation(callee, &candidates, args, &arg_terms, ctx, &path_cond)?;

    if candidates.len() > 1 {
        push_overload_call_obligation(
            callee,
            &candidates,
            args,
            &arg_terms,
            ctx,
            &path_cond,
            call_span,
        )?;
    }

    let fresh = format!("_call_{}", *ctx.call_counter);
    *ctx.call_counter += 1;

    let all_sigs = || candidates.iter().flat_map(|(_, def)| def.sigs.iter());

    // For tuple-returning callees, decompose the result into leaf scalar
    // constants assembled with mk_tuple — same reason as for tuple params:
    // a symbolic tuple constant can't be used with child() extraction.
    let result_var = if let Some(first_sig) = all_sigs().next() {
        if is_product_range(&first_sig.range) {
            let (assembled, leaves) = mk_decomposed_tuple(
                ctx.tm,
                &fresh,
                &first_sig.range,
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
            match set_sort(ctx.tm, &first_sig.range, ctx.distinct_preds, ctx.name_defs) {
                Some(sort) => ctx.tm.mk_const(sort, &fresh),
                None => {
                    return Err(format!(
                        "call to `{}` has an unsupported range sort (internal error)",
                        callee.0
                    ));
                }
            }
        }
    } else {
        ctx.tm.mk_const(ctx.tm.integer_sort(), &fresh)
    };

    for sig in all_sigs() {
        assert_call_contract(sig, &arg_terms, result_var.clone(), ctx);
        if narrow_try && let Some(success) = success_arm_of_range(&sig.range) {
            assert_domain_implies_membership(sig, &arg_terms, result_var.clone(), success, ctx);
        }
    }

    if narrow_try {
        // `result_var` is sorted as the *whole* range (a cross-kind datatype
        // whenever the range has a Fail-shaped arm — always, now that `Fail`
        // is a distinct sort). `?` must yield just the success value, not the
        // tagged wrapper — callers immediately use it as a plain Int/Bool/
        // tuple value (e.g. `y : Nat = f(x)?; y - 1`), which would otherwise
        // build an ill-sorted term against `result_var`'s DT sort.
        let first_sig = all_sigs().next().ok_or_else(|| {
            format!(
                "call to `{}` under `?` has no signature (internal error)",
                callee.0
            )
        })?;
        let success = success_arm_of_range(&first_sig.range).ok_or_else(|| {
            format!(
                "`?` used on a call to `{}`, whose range has no success arm to narrow to",
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
                "cannot narrow `?` on call to `{}`: the success arm's shape doesn't \
             resolve to a single extraction from its range's datatype",
                callee.0
            )
        });
    }

    Ok(result_var)
}

// ── Call-site domain obligation ───────────────────────────────────────────────

/// How one callee signature relates to the arguments of a specific call.
enum DomainMatch<'tm> {
    /// The signature's arity cannot cover this call — it contributes nothing.
    Mismatch,
    /// The domain imposes no constraint on these arguments (e.g. all `Int`
    /// parts against integer-sorted terms) — the obligation is trivially met.
    Trivial,
    /// The arguments belong to this signature's domain iff this term holds.
    Constrained(Term<'tm>),
}

fn sig_domain_match<'tm>(
    sig: &SemFunctionSig,
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    callee: &Symbol,
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Result<DomainMatch<'tm>, String> {
    let parts = match sem_param_set_exprs(sig.domain.as_ref(), arg_terms.len()) {
        Ok(p) => p,
        Err(_) => return Ok(DomainMatch::Mismatch),
    };
    let mut conjuncts: Vec<Term<'_>> = Vec::new();
    for ((arg, term), part) in args.iter().zip(arg_terms).zip(&parts) {
        // Vector-let / runtime-set bindings are opaque integer constants in the
        // solver; a membership constraint built on the raw pointer term would be
        // meaningless (and the scalar-lift path would read it as a length-1
        // sequence). Unknown is the only honest answer until they are value-encoded.
        if matches!(arg.kind_of, ValKind::Vector(_) | ValKind::Set(_)) && term.sort().is_integer() {
            return Err(format!(
                "cannot verify call to `{}`: argument `{}` is an opaque runtime \
                 value the solver does not yet value-encode",
                callee.0, arg
            ));
        }
        match membership_constraint(tm, term.clone(), part, name_defs, distinct_preds) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => conjuncts.push(c),
            Membership::Unsupported => {
                return Err(format!(
                    "cannot verify call to `{}`: domain `{}` uses syntax not yet \
                 supported in the SMT encoding",
                    callee.0, part
                ));
            }
        }
    }
    Ok(match conjuncts.len() {
        0 => DomainMatch::Trivial,
        1 => DomainMatch::Constrained(conjuncts.remove(0)),
        _ => DomainMatch::Constrained(tm.mk_term(Kind::And, &conjuncts)),
    })
}

/// Push the proof obligation that the call's arguments lie in the domain of
/// at least one signature of at least one arity-matching candidate overload.
///
/// Without this obligation the per-signature contracts are vacuous
/// implications: an out-of-domain call (e.g. passing `0` where the domain is
/// `Int - {0}`) would simply fail every antecedent, the callee's body — proved
/// only *under* its domain assumption — would be entered with an input it was
/// never verified against, and the caller would still be reported `proved`.
fn push_call_domain_obligation<'tm>(
    callee: &Symbol,
    candidates: &[(usize, &SemFunctionDef)],
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: &Term<'tm>,
) -> Result<(), String> {
    let mut arms: Vec<Term<'_>> = Vec::new();
    for (_, def) in candidates {
        for sig in &def.sigs {
            match sig_domain_match(
                sig,
                args,
                arg_terms,
                callee,
                ctx.tm,
                ctx.name_defs,
                ctx.distinct_preds,
            )? {
                DomainMatch::Mismatch => {}
                DomainMatch::Trivial => return Ok(()),
                DomainMatch::Constrained(c) => arms.push(c),
            }
        }
    }
    let (obligation, reason) = if arms.is_empty() {
        (
            ctx.tm.mk_boolean(false),
            format!(
                "no signature of `{}` accepts {} argument(s)",
                callee.0,
                arg_terms.len()
            ),
        )
    } else if arms.len() == 1 {
        (
            arms.remove(0),
            format!("arguments to `{}` are not in its declared domain", callee.0),
        )
    } else {
        (
            ctx.tm.mk_term(Kind::Or, &arms),
            format!(
                "arguments to `{}` do not satisfy any of its declared domains",
                callee.0
            ),
        )
    };
    ctx.builtin_obligs.push(BuiltinObligation {
        path_cond: path_cond.clone(),
        obligation,
        violated_reason: reason,
    });
    Ok(())
}

// ── Overload call resolution (int-soundness-plan phase 2) ───────────────────

/// The term "these call arguments lie in `def`'s declared domain" — an OR
/// across `def`'s own signatures (one overload may itself declare more than
/// one signature over one shared body, exactly like today's non-overloaded
/// functions). Unlike `push_call_domain_obligation`'s union-across-candidates
/// obligation, this is scoped to a single candidate, for per-overload
/// call-resolution below.
fn candidate_domain_term<'tm>(
    def: &SemFunctionDef,
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    callee: &Symbol,
    ctx: &EncodeCtx<'_, 'tm>,
) -> Result<Term<'tm>, String> {
    let mut arms: Vec<Term<'_>> = Vec::new();
    for sig in &def.sigs {
        match sig_domain_match(
            sig,
            args,
            arg_terms,
            callee,
            ctx.tm,
            ctx.name_defs,
            ctx.distinct_preds,
        )? {
            DomainMatch::Mismatch => {}
            DomainMatch::Trivial => return Ok(ctx.tm.mk_boolean(true)),
            DomainMatch::Constrained(c) => arms.push(c),
        }
    }
    Ok(match arms.len() {
        0 => ctx.tm.mk_boolean(false),
        1 => arms.remove(0),
        _ => ctx.tm.mk_term(Kind::Or, &arms),
    })
}

/// Record a "which overload does this call resolve to" obligation, decided
/// later (see `encode::decide_overload_resolutions`) — purely an
/// optimization side-channel for codegen, never a soundness requirement (the
/// domain obligation above already guarantees correctness regardless of
/// whether resolution succeeds).
fn push_overload_call_obligation<'tm>(
    callee: &Symbol,
    candidates: &[(usize, &SemFunctionDef)],
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    ctx: &mut EncodeCtx<'_, 'tm>,
    path_cond: &Term<'tm>,
    call_span: Span,
) -> Result<(), String> {
    let mut terms = Vec::with_capacity(candidates.len());
    for (idx, def) in candidates {
        terms.push((
            *idx,
            candidate_domain_term(def, args, arg_terms, callee, ctx)?,
        ));
    }
    ctx.overload_obligs.push(OverloadCallObligation {
        call_span,
        path_cond: path_cond.clone(),
        candidates: terms,
    });
    Ok(())
}

// ── Call contract assertion ───────────────────────────────────────────────────

/// Assert `args ∈ domain → result ∈ range` for one callee signature.
///
/// If any part of the domain or range is unsupported, the implication is
/// silently skipped — the solver has less information but never incorrect info.
/// (The call-site *obligation* that the args actually satisfy some domain is
/// separate — see `push_call_domain_obligation`.)
pub(crate) fn assert_call_contract<'tm>(
    sig: &SemFunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    ctx: &mut EncodeCtx<'_, 'tm>,
) {
    assert_domain_implies_membership(sig, arg_terms, result, &sig.range, ctx);
}

/// Assert `args ∈ sig.domain → result ∈ target_set` as a solver fact.
///
/// Used for both the full call contract (`target_set` = the range) and the
/// `?` success-narrowing (`target_set` = the range's success arm). Arity is
/// matched with the same tuple-vs-scalars rule as parameter binding
/// (`sem_param_set_exprs`); a signature that can't cover this call, or any
/// unsupported membership, skips the fact — fewer facts, never wrong ones.
fn assert_domain_implies_membership<'tm>(
    sig: &SemFunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    target_set: &SemExpr,
    ctx: &mut EncodeCtx<'_, 'tm>,
) {
    let parts = match sem_param_set_exprs(sig.domain.as_ref(), arg_terms.len()) {
        Ok(p) => p,
        Err(_) => return,
    };
    let mut antecedents: Vec<Term<'_>> = Vec::new();
    for (part, arg) in parts.iter().zip(arg_terms.iter()) {
        match membership_constraint(ctx.tm, arg.clone(), part, ctx.name_defs, ctx.distinct_preds) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => antecedents.push(c),
            Membership::Unsupported => return,
        }
    }

    let consequent = match membership_constraint(
        ctx.tm,
        result,
        target_set,
        ctx.name_defs,
        ctx.distinct_preds,
    ) {
        Membership::Unconstrained => return,
        Membership::Constrained(c) => c,
        Membership::Unsupported => return,
    };

    let formula = if antecedents.is_empty() {
        consequent
    } else {
        let antecedent = if antecedents.len() == 1 {
            antecedents.into_iter().next().unwrap()
        } else {
            ctx.tm.mk_term(Kind::And, &antecedents)
        };
        ctx.tm.mk_term(Kind::Implies, &[antecedent, consequent])
    };

    ctx.solver.assert_formula(formula);
}

// ── Distinct-set helpers ──────────────────────────────────────────────────────

/// If `callee` is the auto-generated constructor for a `distinct` set
/// (i.e. its name with the first letter uppercased is a `Distinct` NameDef),
/// return that NameDef.
fn distinct_def_for_constructor<'a>(
    callee: &Symbol,
    name_defs: &'a NameDefs,
) -> Option<&'a crate::semantics::tree::SemNameDef> {
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    let sym = Symbol::new(capitalized);
    name_defs
        .get(&sym)
        .filter(|def| def.kind == DefKind::Distinct)
}

/// If `callee` is the auto-generated constructor for a wrapping fixed-width
/// integer builtin (`signed32(n)`/`unsigned32(n)`,
/// docs/wrapping-and-quotient-sets-plan.md), return its `WrappingInfo`.
/// Unlike `distinct_def_for_constructor`, there's no `NameDef` to look up —
/// `Signed32`/`Unsigned32` are language builtins registered unconditionally
/// in `wrapping` (`build_wrapping_preds`), keyed by the same capitalized name.
fn wrapping_info_for_constructor<'a, 'tm>(
    callee: &Symbol,
    distinct_preds: &'a SolverPreds<'tm>,
) -> Option<&'a super::membership::WrappingInfo<'tm>> {
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    distinct_preds.wrapping.get(&Symbol::new(capitalized))
}

/// If `callee` is `char`, the auto-generated constructor for the builtin
/// `Char` distinct sort (`build_distinct_preds`), return its `DistinctInfo`.
/// Fixed single name, unlike `distinct_def_for_constructor`'s scan over
/// `name_defs` — `Char` is a language builtin, not user-declared.
fn char_info_for_constructor<'a, 'tm>(
    callee: &Symbol,
    distinct_preds: &'a SolverPreds<'tm>,
) -> Option<&'a super::membership::DistinctInfo<'tm>> {
    if callee.0 != "char" {
        return None;
    }
    distinct_preds.get(&Symbol::new("Char"))
}

/// Assert the round-trip identity `from_D(mk_D(arg)) == arg` for one specific
/// constructor call's argument term.
///
/// `mk`/`from` are declared as two independent free uninterpreted functions
/// (`build_distinct_preds`) with no inverse axiom connecting them, so without
/// this the solver has no way to derive e.g. `from(char(65)) == 65` — a
/// ground fact that's true by construction but otherwise invisible to it.
/// Asserted unconditionally (not gated on `path_cond`): it's a definitional
/// property of this call's own `mk`/`from` pair, true regardless of whether
/// the basis obligation on `arg` happens to hold, not a fact about program
/// behaviour along a particular path. Ground (no quantifier) and scoped to
/// this one call's argument term, so it can't cause the quantifier-related
/// hangs `QuotientInfo`'s doc comment warns about — it says nothing about
/// any other application of `mk`/`from`.
pub(crate) fn assert_distinct_round_trip<'tm>(
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    info: &DistinctInfo<'tm>,
    result: &Term<'tm>,
    arg_term: &Term<'tm>,
) {
    let unwrapped = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), result.clone()]);
    let round_trip = tm.mk_term(Kind::Equal, &[unwrapped, arg_term.clone()]);
    solver.assert_formula(round_trip);
}
