//! Block/statement encoding and require/assert checking.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{Expr, ExprKind, FunctionDef, Stmt, collect_loop_modified},
    kind::{Kind as ValKind, set_kind},
    span::Symbol,
};

use super::{CheckResult, NameDefs};
use super::loops::{check_inductive_step, check_for_inductive_step};
use super::encode::{Env, BuiltinObligation, encode_expr, integer_value};
use super::membership::{DistinctPreds, Membership, membership_constraint};

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
    name_defs: &NameDefs<'_>,
    distinct_preds: &DistinctPreds<'tm>,
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
                            membership_constraint(tm, dummy, constraint, name_defs, distinct_preds),
                            Membership::Unconstrained
                        )
                    }
                }
            })
        }
        Stmt::Block(inner) => body_has_unconstrained_loop_var(inner, constraint_env, tm, name_defs, distinct_preds),
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
    name_defs: &NameDefs<'_>,
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
    immutable_names: &mut HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
    // Expected sort for the block's result expression.  Passed to `encode_expr`
    // for `Stmt::Expr` so cross-kind union if/else bodies can be coerced.
    result_sort: Option<Sort<'tm>>,
) -> Result<Option<Term<'tm>>, CheckResult> {
    let top_guard = tm.mk_boolean(true);
    let mut last_expr: Option<Term<'tm>> = None;

    for stmt in stmts {
        last_expr = None; // only the last Expr stmt is the return value
        match stmt {
            Stmt::Let { name, constraint, value: _, .. }
                if matches!(set_kind(constraint), ValKind::Set(_)) =>
            {
                // Immutable runtime set: opaque integer (heap pointer), no value encoding.
                let fresh_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
                immutable_names.insert(name.clone());
                env.insert(name.clone(), fresh);
            }

            Stmt::Let { name, constraint, value, .. } => {
                let val = encode_expr(
                    value, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
                )
                .map_err(CheckResult::Unknown)?;
                let ssa_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                solver.assert_formula(eq.clone());
                accumulated_facts.push(eq);
                // Defer constraint verification to the function-exit check.
                // check_require uses a fresh solver seeded only from accumulated_facts
                // and would miss call contracts added to the main solver — deferring
                // lets the final negation+SAT check use the full solver context.
                if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds) {
                    builtin_obligs.push(BuiltinObligation {
                        path_cond: top_guard.clone(),
                        obligation: c,
                        violated_reason: format!(
                            "initial value of `{}` is not in `{}`",
                            name.0, constraint
                        ),
                    });
                }
                immutable_names.insert(name.clone());
                env.insert(name.clone(), fresh);
            }

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
                    value, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
                )
                .map_err(CheckResult::Unknown)?;
                let ssa_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                solver.assert_formula(eq.clone());
                accumulated_facts.push(eq);
                // Defer constraint verification to the function-exit check.
                // check_require uses a fresh solver seeded only from accumulated_facts
                // and would miss call contracts added to the main solver — deferring
                // lets the final negation+SAT check use the full solver context.
                if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds) {
                    builtin_obligs.push(BuiltinObligation {
                        path_cond: top_guard.clone(),
                        obligation: c,
                        violated_reason: format!(
                            "initial value of `{}` is not in `{}`",
                            name.0, constraint
                        ),
                    });
                }
                constraint_env.insert(name.clone(), constraint.clone());
                env.insert(name.clone(), fresh);
            }

            Stmt::DestructLet { bindings, tuple_constraint, value, .. }
            | Stmt::DestructMutLet { bindings, tuple_constraint, value, .. } => {
                let is_mut = matches!(stmt, Stmt::DestructMutLet { .. });

                let rhs_term = encode_expr(
                    value, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
                ).map_err(CheckResult::Unknown)?;

                // Optional tuple-level constraint (e.g. `x, y : Int * Nat = ...`).
                // The parser currently always emits None; this path is future use.
                if let Some(tc) = tuple_constraint {
                    if let Membership::Constrained(c) = membership_constraint(tm, rhs_term.clone(), tc, name_defs, distinct_preds) {
                        builtin_obligs.push(BuiltinObligation {
                            path_cond: top_guard.clone(),
                            obligation: c,
                            violated_reason: format!("destructured value is not in `{}`", tc),
                        });
                    }
                }

                // child(0) of an APPLY_CONSTRUCTOR tuple is the constructor; elements at child(1+i).
                let tuple_arity = rhs_term.num_children().saturating_sub(1);
                let last_i = bindings.len() - 1;

                for (i, binding) in bindings.iter().enumerate() {
                    let is_tail = i == last_i && bindings.len() < tuple_arity;

                    if is_tail {
                        // Last binder collects remaining elements as a sub-tuple.
                        let tail: Vec<Term<'_>> = (i..tuple_arity)
                            .map(|j| rhs_term.child(j + 1))
                            .collect();
                        let sub_tuple = tm.mk_tuple(&tail);
                        if let Some(constraint) = &binding.constraint {
                            if let Membership::Constrained(c) = membership_constraint(tm, sub_tuple.clone(), constraint, name_defs, distinct_preds) {
                                builtin_obligs.push(BuiltinObligation {
                                    path_cond: top_guard.clone(),
                                    obligation: c,
                                    violated_reason: format!(
                                        "destructured tail `{}` is not in `{}`",
                                        binding.name.0, constraint
                                    ),
                                });
                            }
                        }
                        if is_mut {
                            if let Some(constraint) = &binding.constraint {
                                constraint_env.insert(binding.name.clone(), constraint.clone());
                            }
                        } else {
                            immutable_names.insert(binding.name.clone());
                        }
                        env.insert(binding.name.clone(), sub_tuple);
                    } else {
                        let proj = rhs_term.child(i + 1);
                        let ssa_name = format!("{}_{}", binding.name.0, ssa_counter);
                        *ssa_counter += 1;
                        let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                        let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), proj]);
                        solver.assert_formula(eq.clone());
                        accumulated_facts.push(eq);

                        if let Some(constraint) = &binding.constraint {
                            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds) {
                                builtin_obligs.push(BuiltinObligation {
                                    path_cond: top_guard.clone(),
                                    obligation: c,
                                    violated_reason: format!(
                                        "destructured element {} (`{}`) is not in `{}`",
                                        i, binding.name.0, constraint
                                    ),
                                });
                            }
                        }

                        if is_mut {
                            if let Some(constraint) = &binding.constraint {
                                constraint_env.insert(binding.name.clone(), constraint.clone());
                            }
                        } else {
                            immutable_names.insert(binding.name.clone());
                        }
                        env.insert(binding.name.clone(), fresh);
                    }
                }
            }

            Stmt::DestructAssign { names: dest_names, value, .. } => {
                for name in dest_names.iter() {
                    if immutable_names.contains(name) {
                        return Err(CheckResult::Counterexample {
                            params: HashMap::new(),
                            output: 0,
                            reason: format!(
                                "cannot assign to `{}`: declared as an immutable binding \
                                 (use `mut {}` to allow reassignment)",
                                name.0, name.0
                            ),
                        });
                    }
                    if !env.contains_key(name) {
                        return Err(CheckResult::Unknown(format!(
                            "unbound variable `{}` in destructuring assignment",
                            name.0
                        )));
                    }
                }

                let rhs_term = encode_expr(
                    value, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
                ).map_err(CheckResult::Unknown)?;

                let tuple_arity = rhs_term.num_children().saturating_sub(1);
                let last_i = dest_names.len() - 1;

                for (i, name) in dest_names.iter().enumerate() {
                    let is_tail = i == last_i && dest_names.len() < tuple_arity;

                    if is_tail {
                        // Last binder collects remaining elements as a sub-tuple.
                        let tail: Vec<Term<'_>> = (i..tuple_arity)
                            .map(|j| rhs_term.child(j + 1))
                            .collect();
                        let sub_tuple = tm.mk_tuple(&tail);
                        if let Some(constraint) = constraint_env.get(name).cloned() {
                            if let Membership::Constrained(c) = membership_constraint(tm, sub_tuple.clone(), &constraint, name_defs, distinct_preds) {
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
                                                "`{} :=` (destructured tail) violates declared constraint `{}`",
                                                name.0, constraint
                                            ),
                                        });
                                    }
                                    CheckResult::Unknown(msg) => return Err(CheckResult::Unknown(msg)),
                                }
                            }
                        }
                        env.insert(name.clone(), sub_tuple);
                    } else {
                        let proj = rhs_term.child(i + 1);
                        let ssa_name = format!("{}_{}", name.0, ssa_counter);
                        *ssa_counter += 1;
                        let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                        let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), proj]);
                        solver.assert_formula(eq.clone());
                        accumulated_facts.push(eq);

                        if let Some(constraint) = constraint_env.get(name).cloned() {
                            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), &constraint, name_defs, distinct_preds) {
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
                                                "`{} :=` (destructured) violates declared constraint `{}`",
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
                }
            }

            Stmt::Assign { name, .. } if immutable_names.contains(name) => {
                return Err(CheckResult::Counterexample {
                    params: HashMap::new(),
                    output: 0,
                    reason: format!(
                        "cannot assign to `{}`: declared as an immutable binding \
                         (use `mut {}` to allow reassignment)",
                        name.0, name.0
                    ),
                });
            }

            Stmt::Assign { name, value, .. } => {
                let val = encode_expr(
                    value, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
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
                    if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), &constraint, name_defs, distinct_preds) {
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
                    predicate, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
                )
                .map_err(CheckResult::Unknown)?;
                solver.assert_formula(pred.clone());
                accumulated_facts.push(pred);
            }

            Stmt::Require { predicate, .. } => {
                let pred = encode_expr(
                    predicate, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
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
                    predicate, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None,
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

            Stmt::Return { .. } => {
                // Early returns cannot yet be modelled in the linear-block SMT
                // encoding.  Report Unknown so the solver never silently passes.
                return Err(CheckResult::Unknown(
                    "early `return` not yet supported in the SMT block encoder".into(),
                ));
            }

            Stmt::Expr(e) => {
                let t = encode_expr(
                    e, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, top_guard.clone(), distinct_preds,
                    result_sort.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                last_expr = Some(t);
            }

            Stmt::Block(inner) => {
                last_expr = encode_block(
                    inner, env, name_defs, fn_env, tm, solver,
                    call_counter, builtin_obligs, ssa_counter,
                    accumulated_facts, param_names, param_terms,
                    constraint_env, has_runtime_assert, immutable_names, distinct_preds,
                    result_sort.clone(),
                )?;
            }

            Stmt::While { cond, body, .. } => {
                let modified = collect_loop_modified(body);
                if let Some(step_err) = check_inductive_step(
                    cond, body, &modified, constraint_env,
                    env, accumulated_facts, name_defs, fn_env, tm,
                    ssa_counter, param_names, param_terms, immutable_names, distinct_preds,
                ) {
                    return Err(step_err);
                }

                // Post-loop approximation: replace each loop-modified variable with
                // a fresh constant carrying its declared invariant (justified by the
                // proved inductive step), then assert ¬cond (loop has exited).
                // Immutable names cannot be modified in the loop body; if they appear
                // in `modified` it is a bug that the inductive step check already
                // reported — skip them here.
                for name in &modified {
                    if immutable_names.contains(name) { continue; }
                    if env.contains_key(name) {
                        let fresh_name = format!("{}_{}", name.0, ssa_counter);
                        *ssa_counter += 1;
                        let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
                        if let Some(constraint) = constraint_env.get(name) {
                            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds) {
                                solver.assert_formula(c.clone());
                                accumulated_facts.push(c);
                            }
                        }
                        env.insert(name.clone(), fresh);
                    }
                }

                match encode_expr(cond, env, name_defs, fn_env, tm, solver,
                                  call_counter, builtin_obligs, top_guard.clone(), distinct_preds, None) {
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
                    env, accumulated_facts, name_defs, fn_env, tm,
                    ssa_counter, param_names, param_terms, immutable_names, distinct_preds,
                ) {
                    return Err(step_err);
                }

                // Post-loop: replace each modified var with a fresh constant
                // carrying its declared invariant (justified by the proved step).
                for name in &modified {
                    if immutable_names.contains(name) { continue; }
                    if env.contains_key(name) {
                        let fresh_name = format!("{}_{}", name.0, ssa_counter);
                        *ssa_counter += 1;
                        let fresh = tm.mk_const(tm.integer_sort(), &fresh_name);
                        if let Some(constraint) = constraint_env.get(name) {
                            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds) {
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
    tmp.set_logic("ALL");
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
