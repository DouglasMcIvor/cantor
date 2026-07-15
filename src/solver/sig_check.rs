//! Shared machinery for checking one function signature (domain → range)
//! against its body, for both possible body shapes (`check_sig` for a pure
//! expression body, `check_block_sig` for a block body). See `mod.rs` for
//! the file/function-level orchestration that calls into this module.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::semantics::tree::{SemExpr, SemFunctionSig, sem_param_set_exprs};
use crate::span::{Span, Symbol};

use crate::kind::Kind as ValKind;

use super::blocks::{BlockCtx, body_has_unconstrained_loop_var, encode_block};
use super::disjointness::validate_disjoint_unions;
use super::encode::{
    EncodeCtx, Env, boolean_value, encode_expr, integer_value, mk_decomposed_tuple,
};
use super::membership::{Membership, SolverPreds, membership_constraint};
use super::obligations::{
    BuiltinObligation, OverflowObligation, OverloadCallObligation, decide_overflow_obligations,
    decide_overload_resolutions,
};
use super::preds::build_solver_preds;
use super::sort::set_sort;
use super::{CheckResult, FunctionEnv, NameDefs};

// ── Shared setup/teardown for both signature checkers ────────────────────────
//
// check_sig (pure expression body) and check_block_sig (block body) both:
// configure a fresh solver, build each parameter's solver constant from the
// domain (decomposing tuples into leaf constants), then — after the body is
// encoded by whichever encoder fits the body shape — combine the range
// obligation with any built-in obligations and decode the solver's model into
// a CheckResult. Only the body-encoding step itself differs (encode_expr vs
// encode_block, plus check_block_sig's loop-invariant Unknown carve-out).

/// Configure a solver with the options both checkers need.
/// The single source of cvc5 option configuration for *every* solver
/// instance this module creates — the main per-function solver as well as
/// every isolated sub-query solver (`check_require`, `check_loop_inductive_step`,
/// `validate_disjoint_unions`, `check_name_def`'s constant check, …). Call
/// this rather than hand-rolling `Solver::new` + `set_option` calls: a prior
/// version of this codebase had two sub-query call sites that duplicated
/// this list by hand and silently dropped `mbqi`, which made cvc5 report
/// `Unknown` for completely unrelated counterexample queries whenever a
/// quantified `X*` domain fact merely happened to be in scope (see
/// `docs/design-decisions.md`'s "for x in S loops" section for the
/// post-mortem). One function, called everywhere, closes off that whole
/// class of bug.
pub(super) fn configured_solver<'tm>(tm: &'tm TermManager, timeout_ms: u64) -> Solver<'tm> {
    let mut solver = Solver::new(tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    // nl-cov (libpoly-based covering/CAD) replaces cvc5's default heuristic
    // nonlinear-arithmetic engine, which can hang for minutes on self-multiplication
    // bounds checks (`x * x` against an Int32/Int64-sized range) — see
    // docs/design-decisions.md's nl-cov note.
    solver.set_option("nl-cov", "true");
    if timeout_ms > 0 {
        solver.set_option("tlimit", &timeout_ms.to_string());
    }
    solver
}

/// Build each parameter's solver constant from `domain`, asserting its
/// domain-membership constraint onto `solver`. Tuple params are decomposed
/// into leaf scalar constants assembled with `mk_tuple` — this ensures
/// `TupleProject` in the body always operates on a concrete constructor term
/// (not a symbolic tuple constant), which cvc5's arithmetic beta-reduction
/// requires. Returns `(domain_parts, param_terms)`, both in parameter order —
/// callers need `domain_parts` again later to decode counterexample witnesses
/// by Kind.
fn build_param_terms<'tm, 'e>(
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    domain: Option<&'e SemExpr>,
    param_names: &[Symbol],
    distinct_preds: &SolverPreds<'tm>,
    name_defs: &NameDefs,
) -> Result<(Vec<&'e SemExpr>, Vec<Term<'tm>>), CheckResult> {
    let domain_parts: Vec<&SemExpr> =
        sem_param_set_exprs(domain, param_names.len()).map_err(CheckResult::Unknown)?;

    let mut param_terms: Vec<Term<'_>> = Vec::new();
    for (n, part) in param_names.iter().zip(domain_parts.iter()) {
        let k = part.kind_of.clone();
        if matches!(k, ValKind::Tuple(_)) {
            let (assembled, leaves) =
                mk_decomposed_tuple(tm, &n.0, part, distinct_preds, name_defs);
            for (leaf, leaf_set) in leaves {
                match membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return Err(CheckResult::Unknown(
                            "unsupported domain set expression".into(),
                        ));
                    }
                }
            }
            param_terms.push(assembled);
        } else {
            let sort = match set_sort(tm, part, distinct_preds, name_defs) {
                Some(s) => s,
                None => {
                    return Err(CheckResult::Unknown(format!(
                        "parameter `{}` has an unsupported domain sort (internal error)",
                        n.0
                    )));
                }
            };
            let term = tm.mk_const(sort, &n.0);
            if k != ValKind::Bool {
                match membership_constraint(tm, term.clone(), part, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return Err(CheckResult::Unknown(
                            "unsupported domain set expression".into(),
                        ));
                    }
                }
            }
            param_terms.push(term);
        }
    }

    Ok((domain_parts, param_terms))
}

/// Decode each parameter's solver-model value into the `i64` shown in a
/// `CheckResult::Counterexample`'s `params` map, keyed by Kind.
fn decode_cex_params<'tm>(
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    domain_parts: &[&SemExpr],
    distinct_preds: &SolverPreds<'tm>,
) -> HashMap<String, i64> {
    let mut cex_params = HashMap::new();
    for ((name, term), part) in param_names
        .iter()
        .zip(param_terms.iter())
        .zip(domain_parts.iter())
    {
        let val = solver.get_value(term.clone());
        let k = part.kind_of.clone();
        let n = if k == ValKind::Bool {
            boolean_value(&val) as i64
        } else if matches!(
            k,
            ValKind::Tuple(_) | ValKind::TaggedUnion(_) | ValKind::Vector(_)
        ) {
            // TODO: render tuple/datatype-arm/vector model values in counterexample display
            0
        } else if let Some(info) = distinct_preds
            .wrapping
            .values()
            .find(|i| i.d_sort == term.sort())
        {
            // Parameter has a wrapping (Signed32/Unsigned32) sort — apply
            // `from_D` to recover the BitVec, then the signed/unsigned
            // BitVec→Int reading to get the same decimal value `from(x)`
            // would print.
            let bv_app = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), term.clone()]);
            let to_int_kind = if info.signed {
                Kind::BitvectorSbvToInt
            } else {
                Kind::BitvectorUbvToInt
            };
            let int_app = tm.mk_term(to_int_kind, &[bv_app]);
            integer_value(&solver.get_value(int_app))
        } else if let Some(info) = distinct_preds.values().find(|i| i.sort == term.sort()) {
            // Parameter has a distinct (uninterpreted) sort — apply `from_D` to
            // recover the underlying integer for the counterexample display.
            let from_app = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), term.clone()]);
            integer_value(&solver.get_value(from_app))
        } else {
            integer_value(&val)
        };
        cex_params.insert(name.0.clone(), n);
    }
    cex_params
}

/// The two file-wide proof side-channels (int-soundness-plan phases 1 and 2)
/// threaded through `check_sig`/`check_block_sig`, bundled to keep those
/// functions under clippy's argument-count limit — same fix as the
/// `EncodeCtx`/`BlockCtx`/`LoopCtx` family (see project history).
pub(super) struct SideChannels<'a> {
    pub(super) overflow_checks: &'a mut HashMap<Span, bool>,
    pub(super) overload_resolutions: &'a mut HashMap<Span, Option<usize>>,
}

/// The solver-wide pieces `finish_check`/`decode_cex_params` need, common to
/// both `check_sig` and `check_block_sig`.
struct CheckCtx<'a, 'tm> {
    tm: &'tm TermManager,
    solver: &'a mut Solver<'tm>,
    name_defs: &'a NameDefs,
    distinct_preds: &'a SolverPreds<'tm>,
}

/// One signature's parameter names/solver terms/domain parts, always indexed
/// in parallel — bundled since every consumer (`finish_check`,
/// `decode_cex_params`) reads all three together.
struct SigParams<'a, 'tm> {
    names: &'a [Symbol],
    terms: &'a [Term<'tm>],
    domain_parts: &'a [&'a SemExpr],
}

/// Shared tail of both signature checkers: combine the range obligation with
/// any built-in obligations, ask the solver to refute their conjunction, and
/// turn the result into a `CheckResult`. `extra_unknown_check` runs only on
/// the SAT (counterexample) path, before decoding witness params — it lets
/// `check_block_sig` report its loop-invariant-specific `Unknown` message
/// instead of a generic counterexample when that's the real cause.
fn finish_check<'tm>(
    ctx: &mut CheckCtx<'_, 'tm>,
    body_term: Term<'tm>,
    range: &SemExpr,
    builtin_obligs: &[BuiltinObligation<'tm>],
    params: &SigParams<'_, 'tm>,
    extra_unknown_check: impl FnOnce() -> Option<CheckResult>,
) -> CheckResult {
    let range_obligation = match membership_constraint(
        ctx.tm,
        body_term.clone(),
        range,
        ctx.name_defs,
        ctx.distinct_preds,
    ) {
        Membership::Unconstrained => None,
        Membership::Constrained(c) => Some(c),
        Membership::Unsupported => {
            return CheckResult::Unknown("unsupported range set expression".into());
        }
    };

    let builtin_formulas: Vec<Term<'_>> = builtin_obligs
        .iter()
        .map(|o| {
            if o.path_cond.to_string().trim() == "true" {
                o.obligation.clone()
            } else {
                ctx.tm
                    .mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
            }
        })
        .collect();

    let mut all_obligations: Vec<Term<'_>> = builtin_formulas;
    if let Some(rc) = range_obligation {
        all_obligations.push(rc);
    }

    if all_obligations.is_empty() {
        return CheckResult::Proved;
    }

    let combined = if all_obligations.len() == 1 {
        all_obligations.remove(0)
    } else {
        ctx.tm.mk_term(Kind::And, &all_obligations)
    };
    ctx.solver
        .assert_formula(ctx.tm.mk_term(Kind::Not, &[combined]));

    let sat = ctx.solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        if let Some(early) = extra_unknown_check() {
            return early;
        }
        let cex_params = decode_cex_params(
            ctx.tm,
            ctx.solver,
            params.names,
            params.terms,
            params.domain_parts,
            ctx.distinct_preds,
        );
        let reason = builtin_obligs
            .iter()
            .find(|o| {
                boolean_value(&ctx.solver.get_value(o.path_cond.clone()))
                    && !boolean_value(&ctx.solver.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string())
            .unwrap_or_else(|| format!("not in {}", range));
        let output_term = ctx.solver.get_value(body_term);
        CheckResult::Counterexample {
            params: cex_params,
            output: integer_value(&output_term),
            reason,
        }
    } else {
        CheckResult::Unknown("solver returned unknown".into())
    }
}

/// Every `?`-ed call site in a body requires the *caller's own* declared
/// range to include whichever propagation tag(s) (`Fail`/`None`) the
/// callee's range can produce. Without this, an out-of-contract `?` (e.g.
/// calling a `Nat | None`-returning function from inside a plain `Nat`
/// function) would still "prove" fine — nothing in `encode_call`'s
/// narrowing logic depends on the caller's own range — and then crash
/// codegen with an LLVM return-type mismatch ICE instead of failing here
/// with a clear diagnostic. Mirrors `encode_call`'s own "first
/// arity-matching candidate, first signature" MVP simplification (an
/// overloaded/multi-signature callee is checked only via its first match,
/// same as `narrow_try` itself).
fn check_try_propagation<'a>(
    try_calls: impl Iterator<Item = (&'a Symbol, Span)>,
    sig_range: &SemExpr,
    fn_env: &FunctionEnv<'_>,
) -> Option<CheckResult> {
    use crate::semantics::tree::{range_contains_fail, range_contains_none};
    for (callee, _span) in try_calls {
        let Some(callee_sig) = fn_env
            .get(callee)
            .and_then(|defs| defs.first())
            .and_then(|def| def.sigs.first())
        else {
            continue; // undefined/malformed callee — reported elsewhere
        };
        let missing_fail =
            range_contains_fail(&callee_sig.range) && !range_contains_fail(sig_range);
        let missing_none =
            range_contains_none(&callee_sig.range) && !range_contains_none(sig_range);
        if !missing_fail && !missing_none {
            continue;
        }
        let missing = match (missing_fail, missing_none) {
            (true, true) => "`Fail` and `None`",
            (true, false) => "`Fail`",
            (false, true) => "`None`",
            (false, false) => unreachable!("checked above"),
        };
        return Some(CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: format!(
                "`{}(...)?` can propagate {missing}, but this function's own return type \
                 does not include {missing} — add it to the return type",
                callee.0
            ),
        });
    }
    None
}

// ── Block body checker ────────────────────────────────────────────────────────

pub(super) fn check_block_sig(
    sig: &SemFunctionSig,
    param_names: &[Symbol],
    stmts: &[crate::semantics::tree::SemStmt],
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
    channels: &mut SideChannels<'_>,
) -> CheckResult {
    if let Some(dom) = &sig.domain
        && let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms)
    {
        return result;
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) {
        return result;
    }

    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_solver_preds(&tm, name_defs, fn_env);

    let (domain_parts, param_terms) = match build_param_terms(
        &tm,
        &mut solver,
        sig.domain.as_ref(),
        param_names,
        &distinct_preds,
        name_defs,
    ) {
        Ok(v) => v,
        Err(e) => return e,
    };

    let mut env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let mut overflow_obligs: Vec<OverflowObligation<'_>> = Vec::new();
    let mut overload_obligs: Vec<OverloadCallObligation<'_>> = Vec::new();
    let mut ssa_counter = 0usize;
    let mut constraint_env: HashMap<Symbol, SemExpr> = HashMap::new();
    // Seed constraint_env with each Set(_)/Vector(_)-kind parameter's declared
    // range, so `for x in a_param` can extract the element-kind hypothesis
    // the same way a `mut`-local Set/Vector binding already does (see
    // `blocks.rs`'s `MutLet` arms) — otherwise `check_for_inductive_step`
    // only sees the bare parameter name and has no way to recover its range.
    for (name, part) in param_names.iter().zip(domain_parts.iter()) {
        if matches!(part.kind_of, ValKind::Set(_) | ValKind::Vector(_)) {
            constraint_env.insert(name.clone(), (*part).clone());
        }
    }
    let mut has_runtime_assert = false;
    let mut immutable_names: HashSet<Symbol> = HashSet::new();

    let result_sort = set_sort(&tm, &sig.range, &distinct_preds, name_defs);
    let mut block_ctx = BlockCtx {
        encode: EncodeCtx {
            name_defs,
            fn_env,
            tm: &tm,
            solver: &mut solver,
            call_counter: &mut call_counter,
            builtin_obligs: &mut builtin_obligs,
            overflow_obligs: &mut overflow_obligs,
            overload_obligs: &mut overload_obligs,
            distinct_preds: &distinct_preds,
        },
        ssa_counter: &mut ssa_counter,
        param_names,
        param_terms: &param_terms,
        constraint_env: &mut constraint_env,
        has_runtime_assert: &mut has_runtime_assert,
        immutable_names: &mut immutable_names,
        overflow_checks: channels.overflow_checks,
        overload_resolutions: channels.overload_resolutions,
        timeout_ms,
    };
    let body_term = match encode_block(stmts, &mut env, &mut block_ctx, result_sort) {
        Ok(Some(t)) => t,
        Ok(None) => {
            return CheckResult::Unknown("block body has no return expression".into());
        }
        Err(early) => return early,
    };

    // Decide this signature's flat-statement overflow obligations now, against
    // `solver` as it stands — before `finish_check` asserts the negated
    // correctness goal, which (once proved) would leave `solver` inconsistent
    // and every later query vacuously "proved". Loop bodies already decided
    // their own overflow obligations inline (see `loops.rs`), directly into
    // `overflow_checks`, since they run on an isolated temp solver.
    decide_overflow_obligations(
        &overflow_obligs,
        &tm,
        &solver,
        channels.overflow_checks,
        timeout_ms,
    );
    decide_overload_resolutions(
        &overload_obligs,
        &tm,
        &solver,
        channels.overload_resolutions,
        timeout_ms,
    );

    if has_runtime_assert && !crate::semantics::tree::range_contains_fail(&sig.range) {
        return CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: "assert may fail at runtime but return type does not include `Fail` \
                     — add `| Fail` or use `!!` on the return type, or prove the assertion statically"
                .into(),
        };
    }
    let mut try_calls = Vec::new();
    crate::semantics::tree::collect_try_calls_stmts(stmts, &mut try_calls);
    if let Some(result) = check_try_propagation(try_calls.into_iter(), &sig.range, fn_env) {
        return result;
    }

    let mut check_ctx = CheckCtx {
        tm: &tm,
        solver: &mut solver,
        name_defs,
        distinct_preds: &distinct_preds,
    };
    let sig_params = SigParams {
        names: param_names,
        terms: &param_terms,
        domain_parts: &domain_parts,
    };
    finish_check(
        &mut check_ctx,
        body_term,
        &sig.range,
        &builtin_obligs,
        &sig_params,
        || {
            body_has_unconstrained_loop_var(stmts, &constraint_env, &tm, name_defs, &distinct_preds)
                .then(|| {
                    CheckResult::Unknown(
                        "while loop: declare all mutable variable constraints \
                     (`mut name: Set = expr`) to enable counterexample extraction"
                            .into(),
                    )
                })
        },
    )
}

// ── Pure expression body checker ──────────────────────────────────────────────

pub(super) fn check_sig(
    sig: &SemFunctionSig,
    param_names: &[Symbol],
    body: &SemExpr,
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
    channels: &mut SideChannels<'_>,
) -> CheckResult {
    if let Some(dom) = &sig.domain
        && let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms)
    {
        return result;
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) {
        return result;
    }

    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_solver_preds(&tm, name_defs, fn_env);

    let (domain_parts, param_terms) = match build_param_terms(
        &tm,
        &mut solver,
        sig.domain.as_ref(),
        param_names,
        &distinct_preds,
        name_defs,
    ) {
        Ok(v) => v,
        Err(e) => return e,
    };

    let env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let mut overflow_obligs: Vec<OverflowObligation<'_>> = Vec::new();
    let mut overload_obligs: Vec<OverloadCallObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);
    let range_sort = set_sort(&tm, &sig.range, &distinct_preds, name_defs);
    let mut encode_ctx = EncodeCtx {
        name_defs,
        fn_env,
        tm: &tm,
        solver: &mut solver,
        call_counter: &mut call_counter,
        builtin_obligs: &mut builtin_obligs,
        overflow_obligs: &mut overflow_obligs,
        overload_obligs: &mut overload_obligs,
        distinct_preds: &distinct_preds,
    };
    let body_term = match encode_expr(body, &env, &mut encode_ctx, top_guard, range_sort) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let mut try_calls = Vec::new();
    crate::semantics::tree::collect_try_calls_expr(body, &mut try_calls);
    if let Some(result) = check_try_propagation(try_calls.into_iter(), &sig.range, fn_env) {
        return result;
    }

    // See `check_block_sig`'s identical comment: must run before `finish_check`'s
    // negated-goal assertion.
    decide_overflow_obligations(
        &overflow_obligs,
        &tm,
        &solver,
        channels.overflow_checks,
        timeout_ms,
    );
    decide_overload_resolutions(
        &overload_obligs,
        &tm,
        &solver,
        channels.overload_resolutions,
        timeout_ms,
    );

    let mut check_ctx = CheckCtx {
        tm: &tm,
        solver: &mut solver,
        name_defs,
        distinct_preds: &distinct_preds,
    };
    let sig_params = SigParams {
        names: param_names,
        terms: &param_terms,
        domain_parts: &domain_parts,
    };
    finish_check(
        &mut check_ctx,
        body_term,
        &sig.range,
        &builtin_obligs,
        &sig_params,
        || None,
    )
}
