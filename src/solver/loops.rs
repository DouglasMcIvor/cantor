//! Block/statement encoding and loop invariant checking.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{Expr, ExprKind, FunctionDef, Stmt, collect_loop_modified},
    kind::{Kind as ValKind, set_kind},
    span::Symbol,
};

use super::CheckResult;
use super::encode::{Env, BuiltinObligation, encode_expr, integer_value, boolean_value};
use super::membership::{Membership, membership_constraint};

// ── Loop predicate ────────────────────────────────────────────────────────────

/// Returns `true` when any while or for-in loop in `stmts` modifies a variable
/// that carries no effective SMT constraint.
///
/// When this returns false every loop-modified variable has an inductively-verified
/// binding constraint, so a SAT result from the post-loop check is a genuine
/// counterexample rather than a spurious one caused by a free SMT variable.
pub(crate) fn body_has_unconstrained_loop_var<'tm>(
    stmts: &[Stmt],
    constraint_env: &HashMap<Symbol, Expr>,
    tm: &'tm TermManager,
) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::While { body, .. } | Stmt::ForIn { body, .. } => {
            let modified = collect_loop_modified(body);
            modified.iter().any(|n| {
                match constraint_env.get(n) {
                    None => true,
                    Some(constraint) => {
                        let dummy = tm.mk_integer(0);
                        matches!(
                            membership_constraint(tm, dummy, constraint),
                            Membership::Unconstrained
                        )
                    }
                }
            })
        }
        Stmt::Block(inner) => body_has_unconstrained_loop_var(inner, constraint_env, tm),
        _ => false,
    })
}

// ── Block encoder ─────────────────────────────────────────────────────────────

/// Process a sequence of statements, threading the SSA environment.
///
/// Returns `Ok(Some(term))` where `term` is the last `Stmt::Expr` value,
/// `Ok(None)` if there was no return expression, or `Err(result)` for an
/// early exit (require failure, unsupported construct, etc.).
pub(crate) fn encode_block<'tm>(
    stmts: &[Stmt],
    env: &mut Env<'tm>,
    const_defs: &HashMap<Symbol, &Expr>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    ssa_counter: &mut usize,
    accumulated_facts: &mut Vec<Term<'tm>>,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    constraint_env: &mut HashMap<Symbol, Expr>,
    has_runtime_assert: &mut bool,
) -> Result<Option<Term<'tm>>, CheckResult> {
    let top_guard = tm.mk_boolean(true);
    let mut last_expr: Option<Term<'tm>> = None;

    for stmt in stmts {
        last_expr = None; // only the last Expr stmt is the return value
        match stmt {
            Stmt::MutLet { name, constraint, value: _, .. }
                if matches!(set_kind(constraint), ValKind::Set(_)) =>
            {
                // Runtime set values (Set(Int), Set(Bool)) can't be encoded in
                // QF_NIA. Represent the binding as an opaque integer (the heap
                // pointer) and skip the value encoding and membership assertion.
                let fresh_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
                constraint_env.insert(name.clone(), constraint.clone());
                env.insert(name.clone(), fresh);
            }

            Stmt::MutLet { name, constraint, value, .. } => {
                let val = encode_expr(
                    value, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                let ssa_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                solver.assert_formula(eq.clone());
                accumulated_facts.push(eq);
                // Assert the declared invariant for the initial value.
                if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint) {
                    solver.assert_formula(c.clone());
                    accumulated_facts.push(c);
                }
                constraint_env.insert(name.clone(), constraint.clone());
                env.insert(name.clone(), fresh);
            }

            Stmt::Assign { name, value, .. } => {
                let val = encode_expr(
                    value, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                let ssa_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                solver.assert_formula(eq.clone());
                accumulated_facts.push(eq);
                // Verify (not just trust) that the new value satisfies the declared
                // constraint. Inside loop bodies constraint_env is empty — the
                // inductive step checker handles loop invariants separately — so
                // this check only fires for non-loop reassignments.
                if let Some(constraint) = constraint_env.get(name).cloned() {
                    if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), &constraint) {
                        match check_require(c.clone(), tm, accumulated_facts, param_names, param_terms) {
                            CheckResult::Proved => {
                                solver.assert_formula(c.clone());
                                accumulated_facts.push(c);
                            }
                            CheckResult::Counterexample { params, output, .. } => {
                                return Err(CheckResult::Counterexample {
                                    params,
                                    output,
                                    reason: format!(
                                        "`{} :=` violates declared constraint `{}`",
                                        name.0, constraint
                                    ),
                                });
                            }
                            CheckResult::Unknown(msg) => return Err(CheckResult::Unknown(msg)),
                        }
                    }
                }
                env.insert(name.clone(), fresh);
            }

            Stmt::Assume { predicate, .. } => {
                let pred = encode_expr(
                    predicate, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                solver.assert_formula(pred.clone());
                accumulated_facts.push(pred);
            }

            Stmt::Require { predicate, .. } => {
                let pred = encode_expr(
                    predicate, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(),
                )
                .map_err(CheckResult::Unknown)?;

                match check_require(pred.clone(), tm, accumulated_facts, param_names, param_terms) {
                    CheckResult::Proved => {
                        solver.assert_formula(pred.clone());
                        accumulated_facts.push(pred);
                    }
                    other => return Err(other),
                }
            }

            Stmt::Assert { predicate, .. } => {
                let pred = encode_expr(
                    predicate, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(),
                )
                .map_err(CheckResult::Unknown)?;

                match check_require(pred.clone(), tm, accumulated_facts, param_names, param_terms) {
                    CheckResult::Proved => {
                        // Statically proved — no runtime check needed.
                        solver.assert_formula(pred.clone());
                        accumulated_facts.push(pred);
                    }
                    CheckResult::Counterexample { params, output, .. } => {
                        // pred is not always true.  Check whether NOT(pred) is always
                        // true — if so, pred never holds → compile error.
                        // Otherwise pred is sometimes true → runtime check needed.
                        let not_pred = tm.mk_term(Kind::Not, &[pred.clone()]);
                        match check_require(not_pred, tm, accumulated_facts, param_names, param_terms) {
                            CheckResult::Proved => {
                                return Err(CheckResult::Counterexample {
                                    params,
                                    output,
                                    reason: "assertion always fails".to_string(),
                                });
                            }
                            _ => {
                                // pred is sometimes true — codegen emits a runtime check.
                                *has_runtime_assert = true;
                                solver.assert_formula(pred.clone());
                                accumulated_facts.push(pred);
                            }
                        }
                    }
                    CheckResult::Unknown(_) => {
                        *has_runtime_assert = true;
                        solver.assert_formula(pred.clone());
                        accumulated_facts.push(pred);
                    }
                }
            }

            Stmt::Expr(e) => {
                let t = encode_expr(
                    e, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                last_expr = Some(t);
            }

            Stmt::Block(inner) => {
                last_expr = encode_block(
                    inner, env, const_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, ssa_counter,
                    accumulated_facts, param_names, param_terms,
                    constraint_env, has_runtime_assert,
                )?;
            }

            Stmt::While { cond, body, .. } => {
                let modified = collect_loop_modified(body);
                if let Some(step_err) = check_inductive_step(
                    cond, body, &modified, constraint_env,
                    env, accumulated_facts, const_defs, fn_env, tm,
                    ssa_counter, param_names, param_terms,
                ) {
                    return Err(step_err);
                }

                // Post-loop approximation: replace each loop-modified variable with
                // a fresh constant carrying its declared invariant (justified by the
                // proved inductive step), then assert ¬cond (loop has exited).
                for name in &modified {
                    if env.contains_key(name) {
                        let fresh_name = format!("{}_{}", name.0, ssa_counter);
                        *ssa_counter += 1;
                        let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
                        if let Some(constraint) = constraint_env.get(name) {
                            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint) {
                                solver.assert_formula(c.clone());
                                accumulated_facts.push(c);
                            }
                        }
                        env.insert(name.clone(), fresh);
                    }
                }

                match encode_expr(cond, env, const_defs, fn_env, tm, solver,
                                  call_counter, builtin_obligs, top_guard.clone()) {
                    Ok(cond_term) => {
                        let not_cond = tm.mk_term(Kind::Not, &[cond_term]);
                        solver.assert_formula(not_cond.clone());
                        accumulated_facts.push(not_cond);
                    }
                    Err(_) => {} // cond uses unsupported constructs — skip the fact
                }

                last_expr = None;
            }

            Stmt::ForIn { var, set, body, .. } => {
                // Empty set literal: body never executes, vars are unchanged.
                let is_empty_lit = matches!(&set.kind, ExprKind::SetLit(e) if e.is_empty());
                if is_empty_lit {
                    last_expr = None;
                    continue;
                }

                let modified = collect_loop_modified(body);
                if let Some(step_err) = check_for_inductive_step(
                    var, set, body, &modified, constraint_env,
                    env, accumulated_facts, const_defs, fn_env, tm,
                    ssa_counter, param_names, param_terms,
                ) {
                    return Err(step_err);
                }

                // Post-loop: replace each modified var with a fresh constant
                // carrying its declared invariant (justified by the proved step).
                for name in &modified {
                    if env.contains_key(name) {
                        let fresh_name = format!("{}_{}", name.0, ssa_counter);
                        *ssa_counter += 1;
                        let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
                        if let Some(constraint) = constraint_env.get(name) {
                            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint) {
                                solver.assert_formula(c.clone());
                                accumulated_facts.push(c);
                            }
                        }
                        env.insert(name.clone(), fresh);
                    }
                }

                last_expr = None;
            }
        }
    }

    Ok(last_expr)
}

// ── Require / assert helper ───────────────────────────────────────────────────

/// Run a temporary solver query to check whether `obligation` is provable
/// under `accumulated_facts`.  Returns `Proved`, a `Counterexample`, or
/// `Unknown` — never silently passes an unverified claim.
pub(crate) fn check_require<'tm>(
    obligation: Term<'tm>,
    tm: &'tm TermManager,
    accumulated_facts: &[Term<'tm>],
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
) -> CheckResult {
    let mut tmp = Solver::new(tm);
    tmp.set_logic("QF_NIA");
    tmp.set_option("produce-models", "true");

    for fact in accumulated_facts {
        tmp.assert_formula(fact.clone());
    }
    tmp.assert_formula(tm.mk_term(Kind::Not, &[obligation]));

    let sat = tmp.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        let mut params = HashMap::new();
        for (name, term) in param_names.iter().zip(param_terms.iter()) {
            let val = tmp.get_value(term.clone());
            params.insert(name.0.clone(), integer_value(&val));
        }
        CheckResult::Counterexample {
            params,
            output: 0,
            reason: "requirement failed".to_string(),
        }
    } else {
        CheckResult::Unknown("could not verify requirement".to_string())
    }
}

// ── Inductive step checking ───────────────────────────────────────────────────

/// Common driver for while-loop and for-in inductive-step checks.
///
/// Introduces fresh hypothesis variables for every modified binding, invokes
/// `add_loop_entry` for loop-specific setup (assert condition / bind loop var),
/// encodes one body iteration, then checks that every invariant still holds.
///
/// Returns `None` when UNSAT (step proved); `Some(result)` otherwise.
fn check_loop_inductive_step<'tm, F>(
    body: &[Stmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, Expr>,
    env: &Env<'tm>,
    accumulated_facts: &[Term<'tm>],
    const_defs: &HashMap<Symbol, &Expr>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    inv_label: &str,
    add_loop_entry: F,
) -> Option<CheckResult>
where
    F: FnOnce(
        &mut Solver<'tm>,
        &mut Env<'tm>,
        &mut Vec<Term<'tm>>,
        &mut usize,
    ) -> Option<CheckResult>,
{
    let constrained: Vec<&Symbol> = modified
        .iter()
        .filter(|n| constraint_env.contains_key(*n))
        .collect();
    if constrained.is_empty() {
        return None;
    }

    let mut tmp = Solver::new(tm);
    tmp.set_logic("QF_NIA");
    tmp.set_option("produce-models", "true");

    let mut tmp_facts: Vec<Term<'tm>> = Vec::new();
    for fact in accumulated_facts {
        tmp.assert_formula(fact.clone());
        tmp_facts.push(fact.clone());
    }

    // Fresh inductive-hypothesis variable for each loop-modified binding.
    let mut ind_env = env.clone();
    for name in modified {
        let fresh_name = format!("{}_step_{}", name.0, ssa_counter);
        *ssa_counter += 1;
        let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
        if let Some(constraint) = constraint_env.get(name) {
            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint) {
                tmp.assert_formula(c.clone());
                tmp_facts.push(c);
            }
        }
        ind_env.insert(name.clone(), fresh);
    }

    // Loop-specific setup: assert the condition / introduce the loop variable.
    if let Some(err) = add_loop_entry(&mut tmp, &mut ind_env, &mut tmp_facts, ssa_counter) {
        return Some(err);
    }

    // Encode one body iteration with an empty constraint env — we are checking
    // the invariants, not assuming them.
    let mut body_env = ind_env;
    let mut empty_cenv: HashMap<Symbol, Expr> = HashMap::new();
    let mut cc = 0usize;
    let mut obligs: Vec<BuiltinObligation<'tm>> = Vec::new();
    let mut step_ssa = *ssa_counter;
    let mut _dummy_runtime_assert = false;
    match encode_block(
        body, &mut body_env, const_defs, fn_env, tm, &mut tmp,
        &mut cc, &mut obligs, &mut step_ssa, &mut tmp_facts,
        param_names, param_terms, &mut empty_cenv, &mut _dummy_runtime_assert,
    ) {
        Ok(_) => {}
        Err(e) => return Some(e),
    }
    *ssa_counter = step_ssa;

    // Every constrained var's post-iteration value must satisfy its invariant.
    let mut step_obligs: Vec<Term<'tm>> = Vec::new();
    for name in &constrained {
        if let (Some(constraint), Some(post)) = (constraint_env.get(*name), body_env.get(*name)) {
            if let Membership::Constrained(c) = membership_constraint(tm, post.clone(), constraint) {
                step_obligs.push(c);
            }
        }
    }

    if step_obligs.is_empty() {
        return None;
    }

    let combined = if step_obligs.len() == 1 {
        step_obligs.remove(0)
    } else {
        tm.mk_term(Kind::And, &step_obligs)
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
        let mut reason = format!("{inv_label} not maintained");
        for name in &constrained {
            if let (Some(constraint), Some(post)) = (constraint_env.get(*name), body_env.get(*name)) {
                if let Membership::Constrained(c) = membership_constraint(tm, post.clone(), constraint) {
                    if !boolean_value(&tmp.get_value(c)) {
                        output_val = integer_value(&tmp.get_value(post.clone()));
                        reason = format!(
                            "{inv_label} not maintained: `{}` ∉ {} (value {})",
                            name.0, constraint, output_val
                        );
                        break;
                    }
                }
            }
        }
        Some(CheckResult::Counterexample { params: cex_params, output: output_val, reason })
    } else {
        let names: Vec<&str> = constrained.iter().map(|n| n.0.as_str()).collect();
        Some(CheckResult::Unknown(format!(
            "cannot verify inductive step for {inv_label}s `{}` — \
             add `assert name in Set` inside the loop body to check they hold",
            names.join("`, `")
        )))
    }
}

fn check_inductive_step<'tm>(
    cond: &Expr,
    body: &[Stmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, Expr>,
    env: &Env<'tm>,
    accumulated_facts: &[Term<'tm>],
    const_defs: &HashMap<Symbol, &Expr>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
) -> Option<CheckResult> {
    check_loop_inductive_step(
        body, modified, constraint_env, env, accumulated_facts,
        const_defs, fn_env, tm, ssa_counter, param_names, param_terms,
        "loop invariant",
        |tmp, ind_env, tmp_facts, _ssa| {
            let mut cc = 0usize;
            let mut obligs = Vec::new();
            match encode_expr(cond, ind_env, const_defs, fn_env, tm, tmp,
                              &mut cc, &mut obligs, tm.mk_boolean(true)) {
                Ok(c) => { tmp.assert_formula(c.clone()); tmp_facts.push(c); None }
                Err(_) => Some(CheckResult::Unknown(
                    "cannot verify inductive step: loop condition uses syntax not yet \
                     supported in the SMT encoding".into()
                )),
            }
        },
    )
}

fn check_for_inductive_step<'tm>(
    var: &Symbol,
    set: &Expr,
    body: &[Stmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, Expr>,
    env: &Env<'tm>,
    accumulated_facts: &[Term<'tm>],
    const_defs: &HashMap<Symbol, &Expr>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
) -> Option<CheckResult> {
    check_loop_inductive_step(
        body, modified, constraint_env, env, accumulated_facts,
        const_defs, fn_env, tm, ssa_counter, param_names, param_terms,
        "for-loop invariant",
        |tmp, ind_env, tmp_facts, ssa| {
            let var_fresh_name = format!("{}_iter_{}", var.0, ssa);
            *ssa += 1;
            let var_fresh = tm.mk_const(tm.integer_sort(), &var_fresh_name);
            // When iterating over a runtime set variable, the element kind can't
            // be expressed in QF_NIA. Treat the loop variable as unconstrained.
            let is_runtime_set_var = if let ExprKind::Var(sym) = &set.kind {
                constraint_env.get(sym)
                    .map(|c| matches!(set_kind(c), ValKind::Set(_)))
                    .unwrap_or(false)
            } else {
                false
            };
            if !is_runtime_set_var {
                match membership_constraint(tm, var_fresh.clone(), set) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => { tmp.assert_formula(c.clone()); tmp_facts.push(c); }
                    Membership::Unsupported => return Some(CheckResult::Unknown(
                        "for loop: cannot verify inductive step — iterable set uses syntax \
                         not yet supported in the SMT encoding".into()
                    )),
                }
            }
            ind_env.insert(var.clone(), var_fresh);
            None
        },
    )
}
