//! Loop invariant inductive step checking.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{Expr, ExprKind, FunctionDef, Stmt, collect_loop_modified},
    span::Symbol,
};

use super::{CheckResult, NameDefs};
use super::blocks::{encode_block, check_require};
use super::encode::{Env, BuiltinObligation, encode_expr, integer_value, boolean_value};
use super::membership::{DistinctPreds, Membership, membership_constraint};

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
    name_defs: &NameDefs<'_>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    inv_label: &str,
    outer_immutable_names: &HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
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
    tmp.set_logic("ALL");
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
            if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint, name_defs, distinct_preds) {
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
    // the invariants, not assuming them.  Carry over immutable names from the
    // outer scope so the body can't reassign them.
    let mut body_env = ind_env;
    let mut empty_cenv: HashMap<Symbol, Expr> = HashMap::new();
    let mut step_imm: HashSet<Symbol> = outer_immutable_names.clone();
    let mut cc = 0usize;
    let mut obligs: Vec<BuiltinObligation<'tm>> = Vec::new();
    let mut step_ssa = *ssa_counter;
    let mut _dummy_runtime_assert = false;
    match encode_block(
        body, &mut body_env, name_defs, fn_env, tm, &mut tmp,
        &mut cc, &mut obligs, &mut step_ssa, &mut tmp_facts,
        param_names, param_terms, &mut empty_cenv, &mut _dummy_runtime_assert,
        &mut step_imm, distinct_preds, None,
    ) {
        Ok(_) => {}
        Err(e) => return Some(e),
    }
    *ssa_counter = step_ssa;

    // Every constrained var's post-iteration value must satisfy its invariant.
    let mut step_obligs: Vec<Term<'tm>> = Vec::new();
    for name in &constrained {
        if let (Some(constraint), Some(post)) = (constraint_env.get(*name), body_env.get(*name)) {
            if let Membership::Constrained(c) = membership_constraint(tm, post.clone(), constraint, name_defs, distinct_preds) {
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
                if let Membership::Constrained(c) = membership_constraint(tm, post.clone(), constraint, name_defs, distinct_preds) {
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

pub(super) fn check_inductive_step<'tm>(
    cond: &Expr,
    body: &[Stmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, Expr>,
    env: &Env<'tm>,
    accumulated_facts: &[Term<'tm>],
    name_defs: &NameDefs<'_>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    immutable_names: &HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<CheckResult> {
    check_loop_inductive_step(
        body, modified, constraint_env, env, accumulated_facts,
        name_defs, fn_env, tm, ssa_counter, param_names, param_terms,
        "loop invariant", immutable_names, distinct_preds,
        |tmp, ind_env, tmp_facts, _ssa| {
            let mut cc = 0usize;
            let mut obligs = Vec::new();
            match encode_expr(cond, ind_env, name_defs, fn_env, tm, tmp,
                              &mut cc, &mut obligs, tm.mk_boolean(true), distinct_preds, None) {
                Ok(c) => { tmp.assert_formula(c.clone()); tmp_facts.push(c); None }
                Err(_) => Some(CheckResult::Unknown(
                    "cannot verify inductive step: loop condition uses syntax not yet \
                     supported in the SMT encoding".into()
                )),
            }
        },
    )
}

pub(super) fn check_for_inductive_step<'tm>(
    var: &Symbol,
    set: &Expr,
    body: &[Stmt],
    modified: &HashSet<Symbol>,
    constraint_env: &HashMap<Symbol, Expr>,
    env: &Env<'tm>,
    accumulated_facts: &[Term<'tm>],
    name_defs: &NameDefs<'_>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    ssa_counter: &mut usize,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    immutable_names: &HashSet<Symbol>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<CheckResult> {
    // If `set` is a runtime set variable, extract its element-kind expression
    // from the Set(ElemKind) constraint (e.g. Set(Nat) → Nat, Set(Int-{0}) →
    // Int-{0}).  The clone is cheap — we just need the Expr for membership_constraint.
    let runtime_elem_constraint: Option<Expr> = if let ExprKind::Var(sym) = &set.kind {
        constraint_env.get(sym).and_then(|c| {
            if let ExprKind::Call { callee, args } = &c.kind {
                if callee.0 == "Set" && args.len() == 1 {
                    return Some(args[0].clone());
                }
            }
            None
        })
    } else {
        None
    };

    check_loop_inductive_step(
        body, modified, constraint_env, env, accumulated_facts,
        name_defs, fn_env, tm, ssa_counter, param_names, param_terms,
        "for-loop invariant", immutable_names, distinct_preds,
        |tmp, ind_env, tmp_facts, ssa| {
            let var_fresh_name = format!("{}_iter_{}", var.0, ssa);
            *ssa += 1;
            let var_fresh = tm.mk_const(tm.integer_sort(), &var_fresh_name);
            if let Some(elem_c) = &runtime_elem_constraint {
                // Apply the element-kind constraint (e.g. x >= 0 for Set(Nat)).
                // If the element kind itself is unsupported, proceed unconstrained
                // rather than aborting — we'll just be less precise.
                match membership_constraint(tm, var_fresh.clone(), elem_c, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => { tmp.assert_formula(c.clone()); tmp_facts.push(c); }
                    Membership::Unsupported => {}
                }
            } else {
                match membership_constraint(tm, var_fresh.clone(), set, name_defs, distinct_preds) {
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
