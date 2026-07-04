//! Call-site encoding and domain/contract obligations.
//!
//! Split out of `encode.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — this module holds the
//! call-related machinery (`encode_call` itself, the call-site domain
//! obligation, and callee-contract assertion), while `encode.rs` keeps the
//! expression router and its non-call arms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::DefKind,
    kind::Kind as ValKind,
    semantics::tree::{sem_param_set_exprs, SemExpr, SemFunctionDef, SemFunctionSig},
    span::Symbol,
};

use super::membership::{DistinctPreds, Membership, membership_constraint};
use super::sort::{extract_success_value, is_product_range, maybe_coerce, set_sort, success_arm_of_range};
use super::NameDefs;

use super::encode::{Env, BuiltinObligation, OverflowObligation, encode_expr, mk_decomposed_tuple};

// ── Call encoder ──────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
pub(crate) fn encode_call<'tm>(
    callee: &Symbol,
    args: &[SemExpr],
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    overflow_obligs: &mut Vec<OverflowObligation<'tm>>,
    path_cond: Term<'tm>,
    distinct_preds: &DistinctPreds<'tm>,
    coerce_to: Option<cvc5::Sort<'tm>>,
    // True when this call sits directly under `?`: additionally assert the
    // per-signature success-narrowing `args ∈ domain_i → result ∈ success_arm_i`.
    narrow_try: bool,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, overflow_obligs, path_cond.clone(), distinct_preds, None)
        };
    }

    // Auto-generated constructor: `litre(n)` for `Litre = distinct Nat`.
    // Detected by capitalising the first letter of callee and checking name_defs.
    // Apply the `mk` UF — result has sort D_sort (distinct sort).
    // Emit a basis obligation so `litre(x)` with x : Int is rejected when x ∉ Nat.
    if args.len() == 1 {
        if let Some(distinct_def) = distinct_def_for_constructor(callee, name_defs) {
            if let Some(info) = distinct_preds.get(&distinct_def.name) {
                let arg_term = enc!(&args[0])?;
                match membership_constraint(tm, arg_term.clone(), &distinct_def.value, name_defs, distinct_preds) {
                    Membership::Constrained(c) => builtin_obligs.push(BuiltinObligation {
                        path_cond: path_cond.clone(),
                        obligation: c,
                        violated_reason: format!(
                            "argument to {}() must satisfy the basis constraint",
                            callee.0
                        ),
                    }),
                    Membership::Unconstrained | Membership::Unsupported => {}
                }
                let result = tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), arg_term]);
                // maybe_coerce handles distinct→DT coercion; router's final call is a no-op.
                return maybe_coerce(tm, result, &coerce_to);
            }
        }
    }

    let arg_terms: Vec<Term<'_>> = args.iter().map(|a| enc!(a)).collect::<Result<_, _>>()?;

    let callee_def = fn_env
        .get(callee)
        .ok_or_else(|| format!("unknown function `{}`", callee.0))?;

    push_call_domain_obligation(
        callee, callee_def, args, &arg_terms, tm, name_defs, distinct_preds,
        &path_cond, builtin_obligs,
    )?;

    let fresh = format!("_call_{}", *call_counter);
    *call_counter += 1;

    // For tuple-returning callees, decompose the result into leaf scalar
    // constants assembled with mk_tuple — same reason as for tuple params:
    // a symbolic tuple constant can't be used with child() extraction.
    let result_var = if let Some(first_sig) = callee_def.sigs.first() {
        if is_product_range(&first_sig.range) {
            let (assembled, leaves) = mk_decomposed_tuple(tm, &fresh, &first_sig.range, distinct_preds, name_defs);
            for (leaf, leaf_set) in leaves {
                if let Membership::Constrained(c) =
                    membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds)
                {
                    solver.assert_formula(c);
                }
            }
            assembled
        } else {
            match set_sort(tm, &first_sig.range, distinct_preds, name_defs) {
                Some(sort) => tm.mk_const(sort, &fresh),
                None => return Err(format!(
                    "call to `{}` has an unsupported range sort (internal error)",
                    callee.0
                )),
            }
        }
    } else {
        tm.mk_const(tm.integer_sort(), &fresh)
    };

    for sig in &callee_def.sigs {
        assert_call_contract(sig, &arg_terms, result_var.clone(), tm, solver, name_defs, distinct_preds);
        if narrow_try {
            if let Some(success) = success_arm_of_range(&sig.range) {
                assert_domain_implies_membership(
                    sig, &arg_terms, result_var.clone(), success, tm, solver, name_defs, distinct_preds,
                );
            }
        }
    }

    if narrow_try {
        // `result_var` is sorted as the *whole* range (a cross-kind datatype
        // whenever the range has a Fail-shaped arm — always, now that `Fail`
        // is a distinct sort). `?` must yield just the success value, not the
        // tagged wrapper — callers immediately use it as a plain Int/Bool/
        // tuple value (e.g. `y : Nat = f(x)?; y - 1`), which would otherwise
        // build an ill-sorted term against `result_var`'s DT sort.
        let first_sig = callee_def.sigs.first().ok_or_else(|| {
            format!("call to `{}` under `?` has no signature (internal error)", callee.0)
        })?;
        let success = success_arm_of_range(&first_sig.range).ok_or_else(|| format!(
            "`?` used on a call to `{}`, whose range has no success arm to narrow to",
            callee.0
        ))?;
        return extract_success_value(tm, result_var, success, distinct_preds, name_defs).ok_or_else(|| format!(
            "cannot narrow `?` on call to `{}`: the success arm's shape doesn't \
             resolve to a single extraction from its range's datatype",
            callee.0
        ));
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
    distinct_preds: &DistinctPreds<'tm>,
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
            Membership::Unsupported => return Err(format!(
                "cannot verify call to `{}`: domain `{}` uses syntax not yet \
                 supported in the SMT encoding",
                callee.0, part
            )),
        }
    }
    Ok(match conjuncts.len() {
        0 => DomainMatch::Trivial,
        1 => DomainMatch::Constrained(conjuncts.remove(0)),
        _ => DomainMatch::Constrained(tm.mk_term(Kind::And, &conjuncts)),
    })
}

/// Push the proof obligation that the call's arguments lie in the domain of
/// at least one of the callee's declared signatures.
///
/// Without this obligation the per-signature contracts are vacuous
/// implications: an out-of-domain call (e.g. passing `0` where the domain is
/// `Int - {0}`) would simply fail every antecedent, the callee's body — proved
/// only *under* its domain assumption — would be entered with an input it was
/// never verified against, and the caller would still be reported `proved`.
#[allow(clippy::too_many_arguments)]
fn push_call_domain_obligation<'tm>(
    callee: &Symbol,
    callee_def: &SemFunctionDef,
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
    path_cond: &Term<'tm>,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
) -> Result<(), String> {
    let mut arms: Vec<Term<'_>> = Vec::new();
    for sig in &callee_def.sigs {
        match sig_domain_match(sig, args, arg_terms, callee, tm, name_defs, distinct_preds)? {
            DomainMatch::Mismatch => {}
            DomainMatch::Trivial => return Ok(()),
            DomainMatch::Constrained(c) => arms.push(c),
        }
    }
    let (obligation, reason) = if arms.is_empty() {
        (
            tm.mk_boolean(false),
            format!("no signature of `{}` accepts {} argument(s)", callee.0, arg_terms.len()),
        )
    } else if arms.len() == 1 {
        (
            arms.remove(0),
            format!("arguments to `{}` are not in its declared domain", callee.0),
        )
    } else {
        (
            tm.mk_term(Kind::Or, &arms),
            format!("arguments to `{}` do not satisfy any of its declared domains", callee.0),
        )
    };
    builtin_obligs.push(BuiltinObligation {
        path_cond: path_cond.clone(),
        obligation,
        violated_reason: reason,
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
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
) {
    assert_domain_implies_membership(sig, arg_terms, result, &sig.range, tm, solver, name_defs, distinct_preds);
}

/// Assert `args ∈ sig.domain → result ∈ target_set` as a solver fact.
///
/// Used for both the full call contract (`target_set` = the range) and the
/// `?` success-narrowing (`target_set` = the range's success arm). Arity is
/// matched with the same tuple-vs-scalars rule as parameter binding
/// (`sem_param_set_exprs`); a signature that can't cover this call, or any
/// unsupported membership, skips the fact — fewer facts, never wrong ones.
#[allow(clippy::too_many_arguments)]
fn assert_domain_implies_membership<'tm>(
    sig: &SemFunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    target_set: &SemExpr,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
) {
    let parts = match sem_param_set_exprs(sig.domain.as_ref(), arg_terms.len()) {
        Ok(p) => p,
        Err(_) => return,
    };
    let mut antecedents: Vec<Term<'_>> = Vec::new();
    for (part, arg) in parts.iter().zip(arg_terms.iter()) {
        match membership_constraint(tm, arg.clone(), part, name_defs, distinct_preds) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => antecedents.push(c),
            Membership::Unsupported => return,
        }
    }

    let consequent = match membership_constraint(tm, result, target_set, name_defs, distinct_preds) {
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
            tm.mk_term(Kind::And, &antecedents)
        };
        tm.mk_term(Kind::Implies, &[antecedent, consequent])
    };

    solver.assert_formula(formula);
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
    name_defs.get(&sym).filter(|def| def.kind == DefKind::Distinct)
}
