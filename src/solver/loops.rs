//! Loop invariant inductive step checking.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    semantics::{
        builtins,
        tree::{SemExpr, SemExprKind, SemFunctionDef, SemStmt},
    },
    span::{Span, Symbol},
};

use super::blocks::{BlockCtx, encode_block};
use super::encode::{EncodeCtx, Env, boolean_value, encode_expr, integer_value};
use super::membership::{Membership, SolverPreds, membership_constraint};
use super::obligations::{
    BuiltinObligation, OverflowObligation, OverloadCallObligation, decide_overflow_obligations,
    decide_overload_resolutions,
};
use super::{CheckResult, NameDefs};

/// Everything `check_inductive_step`/`check_for_inductive_step` (and their
/// shared driver `check_loop_inductive_step`) thread unchanged through one
/// loop's inductive-step check. Deliberately separate from `EncodeCtx`: the
/// step check runs against a fresh, isolated solver seeded from
/// `outer_solver`'s assertions (see `check_loop_inductive_step`'s module
/// doc), so `outer_solver` is a shared reference here, never the `&mut
/// Solver` `EncodeCtx` holds.
pub(super) struct LoopCtx<'a, 'tm> {
    pub(super) constraint_env: &'a HashMap<Symbol, SemExpr>,
    pub(super) name_defs: &'a NameDefs,
    pub(super) fn_env: &'a HashMap<Symbol, Vec<&'a SemFunctionDef>>,
    pub(super) tm: &'tm TermManager,
    pub(super) outer_solver: &'a Solver<'tm>,
    pub(super) ssa_counter: &'a mut usize,
    pub(super) param_names: &'a [Symbol],
    pub(super) param_terms: &'a [Term<'tm>],
    pub(super) immutable_names: &'a HashSet<Symbol>,
    pub(super) distinct_preds: &'a SolverPreds<'tm>,
    pub(super) has_runtime_assert: &'a mut bool,
    pub(super) overflow_checks: &'a mut HashMap<Span, bool>,
    pub(super) overload_resolutions: &'a mut HashMap<Span, Option<usize>>,
    pub(super) timeout_ms: u64,
}

// ── Inductive step checking ───────────────────────────────────────────────────

/// Common driver for while-loop and for-in inductive-step checks.
///
/// Introduces fresh hypothesis variables for every modified binding, invokes
/// `add_loop_entry` for loop-specific setup (assert condition / bind loop var),
/// encodes one body iteration, then checks — under the same hypothesis — that
/// every invariant still holds AND that every built-in obligation the body
/// produced (division domains, vector bounds, call-site domains, …) is met.
/// The hypothesis (invariants + loop condition + outer facts) over-approximates
/// every reachable iteration, so obligations proved here hold on all of them;
/// dropping them instead was a false-proof hole.
///
/// Returns `None` when UNSAT (step proved); `Some(result)` otherwise.
fn check_loop_inductive_step<'tm, F>(
    body: &[SemStmt],
    modified: &HashSet<Symbol>,
    env: &Env<'tm>,
    ctx: &mut LoopCtx<'_, 'tm>,
    inv_label: &str,
    add_loop_entry: F,
) -> Option<CheckResult>
where
    F: FnOnce(
        &mut Solver<'tm>,
        &mut Env<'tm>,
        &mut usize,
        &mut Vec<OverflowObligation<'tm>>,
        &mut Vec<OverloadCallObligation<'tm>>,
    ) -> Option<CheckResult>,
{
    // Even when no modified variable carries an invariant, the body must still
    // be encoded: its built-in obligations need discharging regardless.
    let constrained: Vec<&Symbol> = modified
        .iter()
        .filter(|n| ctx.constraint_env.contains_key(*n))
        .collect();

    let mut tmp = Solver::new(ctx.tm);
    tmp.set_logic("ALL");
    tmp.set_option("produce-models", "true");
    // See `check_name_def`'s comment in mod.rs for the mbqi rationale — any
    // fact seeded from `ctx.outer_solver`'s assertions below may include a
    // quantified `X*` domain constraint (from an unrelated vector parameter),
    // and without MBQI cvc5 can report Unknown even for a query that has
    // nothing to do with that quantifier.
    tmp.set_option("mbqi", "true");
    // See `check_name_def`'s comment in mod.rs for the nl-cov rationale.
    tmp.set_option("nl-cov", "true");
    if ctx.timeout_ms > 0 {
        tmp.set_option("tlimit", &ctx.timeout_ms.to_string());
    }

    // Seed from everything asserted on the enclosing solver so far — not just
    // a separately-threaded fact list — so call contracts established before
    // the loop (asserted straight onto `outer_solver` by `assert_call_contract`)
    // are visible here too. Same fix as `check_require`'s in blocks.rs.
    for fact in ctx.outer_solver.get_assertions() {
        tmp.assert_formula(fact);
    }

    // Fresh inductive-hypothesis variable for each loop-modified binding.
    let mut ind_env = env.clone();
    for name in modified {
        let fresh_name = format!("{}_step_{}", name.0, ctx.ssa_counter);
        *ctx.ssa_counter += 1;
        // The hypothesis variable carries the binding's actual solver sort
        // (Bool muts are boolean-sorted, tuple muts tuple-sorted); a name not
        // in the outer env is declared inside the body and will be shadowed.
        let sort = env
            .get(name)
            .map(|t| t.sort())
            .unwrap_or_else(|| ctx.tm.integer_sort());
        let fresh = ctx.tm.mk_const(sort, &fresh_name);
        if let Some(constraint) = ctx.constraint_env.get(name)
            && let Membership::Constrained(c) = membership_constraint(
                ctx.tm,
                fresh.clone(),
                constraint,
                ctx.name_defs,
                ctx.distinct_preds,
            )
        {
            tmp.assert_formula(c.clone());
        }
        ind_env.insert(name.clone(), fresh);
    }

    // Collects overflow obligations from both the loop-entry closure (e.g. the
    // `while` condition) and the body below — decided together in one pass
    // against `tmp` once encoding finishes, before the correctness check's
    // negated-goal assertion makes `tmp` inconsistent (see below).
    let mut overflow_obligs: Vec<OverflowObligation<'tm>> = Vec::new();
    let mut overload_obligs: Vec<OverloadCallObligation<'tm>> = Vec::new();

    // Loop-specific setup: assert the condition / introduce the loop variable.
    if let Some(err) = add_loop_entry(
        &mut tmp,
        &mut ind_env,
        ctx.ssa_counter,
        &mut overflow_obligs,
        &mut overload_obligs,
    ) {
        return Some(err);
    }

    // Encode one body iteration with an empty constraint env — we are checking
    // the invariants, not assuming them.  Carry over immutable names from the
    // outer scope so the body can't reassign them.
    let mut body_env = ind_env;
    let mut empty_cenv: HashMap<Symbol, SemExpr> = HashMap::new();
    let mut step_imm: HashSet<Symbol> = ctx.immutable_names.clone();
    let mut cc = 0usize;
    let mut obligs: Vec<BuiltinObligation<'tm>> = Vec::new();
    let mut step_ssa = *ctx.ssa_counter;
    // An unproved `assert` inside the body needs `| Fail` on the range exactly
    // like one in a flat block — the flag must reach the function-level check.
    let step_result = {
        let encode_ctx = EncodeCtx {
            name_defs: ctx.name_defs,
            fn_env: ctx.fn_env,
            tm: ctx.tm,
            solver: &mut tmp,
            call_counter: &mut cc,
            builtin_obligs: &mut obligs,
            overflow_obligs: &mut overflow_obligs,
            overload_obligs: &mut overload_obligs,
            distinct_preds: ctx.distinct_preds,
        };
        let mut block_ctx = BlockCtx {
            encode: encode_ctx,
            ssa_counter: &mut step_ssa,
            param_names: ctx.param_names,
            param_terms: ctx.param_terms,
            constraint_env: &mut empty_cenv,
            has_runtime_assert: ctx.has_runtime_assert,
            immutable_names: &mut step_imm,
            overflow_checks: ctx.overflow_checks,
            overload_resolutions: ctx.overload_resolutions,
            timeout_ms: ctx.timeout_ms,
        };
        encode_block(body, &mut body_env, &mut block_ctx, None)
    };
    match step_result {
        Ok(_) => {}
        Err(e) => return Some(e),
    }
    *ctx.ssa_counter = step_ssa;

    // Decide overflow obligations from this body iteration now, against `tmp`
    // as it stands (hypothesis vars + loop entry + body facts) — before the
    // correctness check below asserts the negated goal onto `tmp`, which
    // would make its assertion set inconsistent and every later query
    // vacuously "proved".
    decide_overflow_obligations(
        &overflow_obligs,
        ctx.tm,
        &tmp,
        ctx.overflow_checks,
        ctx.timeout_ms,
    );
    decide_overload_resolutions(
        &overload_obligs,
        ctx.tm,
        &tmp,
        ctx.overload_resolutions,
        ctx.timeout_ms,
    );

    // Every constrained var's post-iteration value must satisfy its invariant.
    let mut step_obligs: Vec<Term<'tm>> = Vec::new();
    for name in &constrained {
        if let (Some(constraint), Some(post)) = (ctx.constraint_env.get(*name), body_env.get(*name))
            && let Membership::Constrained(c) = membership_constraint(
                ctx.tm,
                post.clone(),
                constraint,
                ctx.name_defs,
                ctx.distinct_preds,
            )
        {
            step_obligs.push(c);
        }
    }

    // Body built-in obligations, path-conditioned like the function-level check.
    let mut all_obligs: Vec<Term<'tm>> = obligs
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
    all_obligs.extend(step_obligs);

    if all_obligs.is_empty() {
        return None;
    }

    let combined = if all_obligs.len() == 1 {
        all_obligs.remove(0)
    } else {
        ctx.tm.mk_term(Kind::And, &all_obligs)
    };
    tmp.assert_formula(ctx.tm.mk_term(Kind::Not, &[combined]));

    let sat = tmp.check_sat();
    if sat.is_unsat() {
        None
    } else if sat.is_sat() {
        let mut cex_params: HashMap<String, i64> = HashMap::new();
        for (name, term) in ctx.param_names.iter().zip(ctx.param_terms.iter()) {
            let val = tmp.get_value(term.clone());
            cex_params.insert(name.0.clone(), integer_value(&val));
        }
        let mut output_val = 0i64;
        // A violated built-in obligation is the root cause — the invariant
        // break (if any) is usually downstream of it, so it wins the reason.
        let mut reason = obligs
            .iter()
            .find(|o| {
                boolean_value(&tmp.get_value(o.path_cond.clone()))
                    && !boolean_value(&tmp.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string());
        if reason.is_none() {
            for name in &constrained {
                if let (Some(constraint), Some(post)) =
                    (ctx.constraint_env.get(*name), body_env.get(*name))
                    && let Membership::Constrained(c) = membership_constraint(
                        ctx.tm,
                        post.clone(),
                        constraint,
                        ctx.name_defs,
                        ctx.distinct_preds,
                    )
                    && !boolean_value(&tmp.get_value(c))
                {
                    output_val = integer_value(&tmp.get_value(post.clone()));
                    reason = Some(format!(
                        "{inv_label} not maintained: `{}` ∉ {} (value {})",
                        name.0, constraint, output_val
                    ));
                    break;
                }
            }
        }
        let reason = reason.unwrap_or_else(|| format!("{inv_label} not maintained"));
        Some(CheckResult::Counterexample {
            params: cex_params,
            output: output_val,
            reason,
        })
    } else if constrained.is_empty() {
        Some(CheckResult::Unknown(format!(
            "cannot verify built-in obligations inside the {inv_label} body",
        )))
    } else {
        let names: Vec<&str> = constrained.iter().map(|n| n.0.as_str()).collect();
        Some(CheckResult::Unknown(format!(
            "cannot verify inductive step for {inv_label}s `{}` — \
             add `assert name in Set` inside the loop body to check they hold",
            names.join("`, `")
        )))
    }
}

pub(super) fn check_inductive_step<'tm>(
    cond: &SemExpr,
    body: &[SemStmt],
    modified: &HashSet<Symbol>,
    env: &Env<'tm>,
    ctx: &mut LoopCtx<'_, 'tm>,
) -> Option<CheckResult> {
    let name_defs = ctx.name_defs;
    let fn_env = ctx.fn_env;
    let tm = ctx.tm;
    let distinct_preds = ctx.distinct_preds;
    check_loop_inductive_step(
        body,
        modified,
        env,
        ctx,
        "loop invariant",
        |tmp, ind_env, _ssa, overflow_obligs, overload_obligs| {
            let mut cc = 0usize;
            let mut obligs = Vec::new();
            let mut encode_ctx = EncodeCtx {
                name_defs,
                fn_env,
                tm,
                solver: tmp,
                call_counter: &mut cc,
                builtin_obligs: &mut obligs,
                overflow_obligs,
                overload_obligs,
                distinct_preds,
            };
            match encode_expr(cond, ind_env, &mut encode_ctx, tm.mk_boolean(true), None) {
                Ok(c) => {
                    encode_ctx.solver.assert_formula(c.clone());
                    None
                }
                Err(_) => Some(CheckResult::Unknown(
                    "cannot verify inductive step: loop condition uses syntax not yet \
                     supported in the SMT encoding"
                        .into(),
                )),
            }
        },
    )
}

pub(super) fn check_for_inductive_step<'tm>(
    var: &Symbol,
    set: &SemExpr,
    body: &[SemStmt],
    modified: &HashSet<Symbol>,
    env: &Env<'tm>,
    ctx: &mut LoopCtx<'_, 'tm>,
) -> Option<CheckResult> {
    // If `set` is a runtime set variable, extract its element-kind expression
    // from the Set(ElemKind) constraint (e.g. Set(Nat) → Nat, Set(Int-{0}) →
    // Int-{0}).  The clone is cheap — we just need the Expr for membership_constraint.
    let runtime_elem_constraint: Option<SemExpr> = if let SemExprKind::Var(sym) = &set.kind {
        ctx.constraint_env.get(sym).and_then(|c| {
            if let SemExprKind::Call { callee, args } = &c.kind
                && callee.0 == builtins::SET_CONSTRUCTOR
                && args.len() == 1
            {
                return Some(args[0].clone());
            }
            // Vector iteration (`X*`, parameter or `mut` local): the
            // declared constraint is the raw `KleeneStar(elem)` set
            // expression (see `mod.rs`'s constraint_env seeding for
            // Vector-kind params, and `blocks.rs`'s `MutLet` handling for
            // Vector-kind locals) — extract `elem` as the per-iteration
            // hypothesis, same role as `Set(elem)`'s `args[0]` above.
            if let SemExprKind::KleeneStar(elem) = &c.kind {
                return Some((**elem).clone());
            }
            None
        })
    } else {
        None
    };

    let name_defs = ctx.name_defs;
    let tm = ctx.tm;
    let distinct_preds = ctx.distinct_preds;
    check_loop_inductive_step(
        body,
        modified,
        env,
        ctx,
        "for-loop invariant",
        |tmp, ind_env, ssa, _overflow_obligs, _overload_obligs| {
            let var_fresh_name = format!("{}_iter_{}", var.0, ssa);
            *ssa += 1;
            let var_fresh = tm.mk_const(tm.integer_sort(), &var_fresh_name);
            if let Some(elem_c) = &runtime_elem_constraint {
                // Apply the element-kind constraint (e.g. x >= 0 for Set(Nat)).
                // If the element kind itself is unsupported, proceed unconstrained
                // rather than aborting — we'll just be less precise.
                match membership_constraint(
                    tm,
                    var_fresh.clone(),
                    elem_c,
                    name_defs,
                    distinct_preds,
                ) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => {
                        tmp.assert_formula(c.clone());
                    }
                    Membership::Unsupported => {}
                }
            } else {
                match membership_constraint(tm, var_fresh.clone(), set, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => {
                        tmp.assert_formula(c.clone());
                    }
                    Membership::Unsupported => {
                        return Some(CheckResult::Unknown(
                            "for loop: cannot verify inductive step — iterable set uses syntax \
                         not yet supported in the SMT encoding"
                                .into(),
                        ));
                    }
                }
            }
            ind_env.insert(var.clone(), var_fresh);
            None
        },
    )
}
