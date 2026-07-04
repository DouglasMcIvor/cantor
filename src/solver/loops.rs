//! Loop invariant inductive step checking.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    semantics::tree::{SemExpr, SemExprKind, SemFunctionDef, SemStmt},
    span::{Span, Symbol},
};

use super::blocks::encode_block;
use super::encode::{
    BuiltinObligation, Env, OverflowObligation, boolean_value, decide_overflow_obligations,
    encode_expr, integer_value,
};
use super::membership::{DistinctPreds, Membership, membership_constraint};
use super::{CheckResult, NameDefs};

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
#[allow(clippy::too_many_arguments)]
fn check_loop_inductive_step<'tm, F>(
    body: &[SemStmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, SemExpr>,
    env: &Env<'tm>,
    outer_solver: &Solver<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    inv_label: &str,
    outer_immutable_names: &HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
    has_runtime_assert: &mut bool,
    overflow_checks: &mut HashMap<Span, bool>,
    add_loop_entry: F,
) -> Option<CheckResult>
where
    F: FnOnce(
        &mut Solver<'tm>,
        &mut Env<'tm>,
        &mut usize,
        &mut Vec<OverflowObligation<'tm>>,
    ) -> Option<CheckResult>,
{
    // Even when no modified variable carries an invariant, the body must still
    // be encoded: its built-in obligations need discharging regardless.
    let constrained: Vec<&Symbol> = modified
        .iter()
        .filter(|n| constraint_env.contains_key(*n))
        .collect();

    let mut tmp = Solver::new(tm);
    tmp.set_logic("ALL");
    tmp.set_option("produce-models", "true");

    // Seed from everything asserted on the enclosing solver so far — not just
    // a separately-threaded fact list — so call contracts established before
    // the loop (asserted straight onto `outer_solver` by `assert_call_contract`)
    // are visible here too. Same fix as `check_require`'s in blocks.rs.
    for fact in outer_solver.get_assertions() {
        tmp.assert_formula(fact);
    }

    // Fresh inductive-hypothesis variable for each loop-modified binding.
    let mut ind_env = env.clone();
    for name in modified {
        let fresh_name = format!("{}_step_{}", name.0, ssa_counter);
        *ssa_counter += 1;
        // The hypothesis variable carries the binding's actual solver sort
        // (Bool muts are boolean-sorted, tuple muts tuple-sorted); a name not
        // in the outer env is declared inside the body and will be shadowed.
        let sort = env
            .get(name)
            .map(|t| t.sort())
            .unwrap_or_else(|| tm.integer_sort());
        let fresh = tm.mk_const(sort, &fresh_name);
        if let Some(constraint) = constraint_env.get(name)
            && let Membership::Constrained(c) =
                membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds)
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

    // Loop-specific setup: assert the condition / introduce the loop variable.
    if let Some(err) = add_loop_entry(&mut tmp, &mut ind_env, ssa_counter, &mut overflow_obligs) {
        return Some(err);
    }

    // Encode one body iteration with an empty constraint env — we are checking
    // the invariants, not assuming them.  Carry over immutable names from the
    // outer scope so the body can't reassign them.
    let mut body_env = ind_env;
    let mut empty_cenv: HashMap<Symbol, SemExpr> = HashMap::new();
    let mut step_imm: HashSet<Symbol> = outer_immutable_names.clone();
    let mut cc = 0usize;
    let mut obligs: Vec<BuiltinObligation<'tm>> = Vec::new();
    let mut step_ssa = *ssa_counter;
    // An unproved `assert` inside the body needs `| Fail` on the range exactly
    // like one in a flat block — the flag must reach the function-level check.
    match encode_block(
        body,
        &mut body_env,
        name_defs,
        fn_env,
        tm,
        &mut tmp,
        &mut cc,
        &mut obligs,
        &mut overflow_obligs,
        &mut step_ssa,
        param_names,
        param_terms,
        &mut empty_cenv,
        has_runtime_assert,
        &mut step_imm,
        distinct_preds,
        overflow_checks,
        None,
    ) {
        Ok(_) => {}
        Err(e) => return Some(e),
    }
    *ssa_counter = step_ssa;

    // Decide overflow obligations from this body iteration now, against `tmp`
    // as it stands (hypothesis vars + loop entry + body facts) — before the
    // correctness check below asserts the negated goal onto `tmp`, which
    // would make its assertion set inconsistent and every later query
    // vacuously "proved".
    decide_overflow_obligations(&overflow_obligs, tm, &tmp, overflow_checks);

    // Every constrained var's post-iteration value must satisfy its invariant.
    let mut step_obligs: Vec<Term<'tm>> = Vec::new();
    for name in &constrained {
        if let (Some(constraint), Some(post)) = (constraint_env.get(*name), body_env.get(*name))
            && let Membership::Constrained(c) =
                membership_constraint(tm, post.clone(), constraint, name_defs, distinct_preds)
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
                tm.mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
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
        tm.mk_term(Kind::And, &all_obligs)
    };
    tmp.assert_formula(tm.mk_term(Kind::Not, &[combined]));

    let sat = tmp.check_sat();
    if sat.is_unsat() {
        None
    } else if sat.is_sat() {
        let mut cex_params: HashMap<String, i64> = HashMap::new();
        for (name, term) in param_names.iter().zip(param_terms.iter()) {
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
                    (constraint_env.get(*name), body_env.get(*name))
                    && let Membership::Constrained(c) = membership_constraint(
                        tm,
                        post.clone(),
                        constraint,
                        name_defs,
                        distinct_preds,
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

// TODO: 16 params is a clippy::too_many_arguments smell; consider bundling the
// solver-wide context (env, name_defs, fn_env, tm, distinct_preds, ...) into a
// struct threaded through this module once the encoding pipeline settles down.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_inductive_step<'tm>(
    cond: &SemExpr,
    body: &[SemStmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, SemExpr>,
    env: &Env<'tm>,
    outer_solver: &Solver<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    immutable_names: &HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
    has_runtime_assert: &mut bool,
    overflow_checks: &mut HashMap<Span, bool>,
) -> Option<CheckResult> {
    check_loop_inductive_step(
        body,
        modified,
        constraint_env,
        env,
        outer_solver,
        name_defs,
        fn_env,
        tm,
        ssa_counter,
        param_names,
        param_terms,
        "loop invariant",
        immutable_names,
        distinct_preds,
        has_runtime_assert,
        overflow_checks,
        |tmp, ind_env, _ssa, overflow_obligs| {
            let mut cc = 0usize;
            let mut obligs = Vec::new();
            match encode_expr(
                cond,
                ind_env,
                name_defs,
                fn_env,
                tm,
                tmp,
                &mut cc,
                &mut obligs,
                overflow_obligs,
                tm.mk_boolean(true),
                distinct_preds,
                None,
            ) {
                Ok(c) => {
                    tmp.assert_formula(c.clone());
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

// TODO: same too-many-arguments smell as check_inductive_step above.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_for_inductive_step<'tm>(
    var: &Symbol,
    set: &SemExpr,
    body: &[SemStmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, SemExpr>,
    env: &Env<'tm>,
    outer_solver: &Solver<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    immutable_names: &HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
    has_runtime_assert: &mut bool,
    overflow_checks: &mut HashMap<Span, bool>,
) -> Option<CheckResult> {
    // If `set` is a runtime set variable, extract its element-kind expression
    // from the Set(ElemKind) constraint (e.g. Set(Nat) → Nat, Set(Int-{0}) →
    // Int-{0}).  The clone is cheap — we just need the Expr for membership_constraint.
    let runtime_elem_constraint: Option<SemExpr> = if let SemExprKind::Var(sym) = &set.kind {
        constraint_env.get(sym).and_then(|c| {
            if let SemExprKind::Call { callee, args } = &c.kind
                && callee.0 == "Set"
                && args.len() == 1
            {
                return Some(args[0].clone());
            }
            None
        })
    } else {
        None
    };

    check_loop_inductive_step(
        body,
        modified,
        constraint_env,
        env,
        outer_solver,
        name_defs,
        fn_env,
        tm,
        ssa_counter,
        param_names,
        param_terms,
        "for-loop invariant",
        immutable_names,
        distinct_preds,
        has_runtime_assert,
        overflow_checks,
        |tmp, ind_env, ssa, _overflow_obligs| {
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
