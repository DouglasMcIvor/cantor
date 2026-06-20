//! Domain/range constraint checker using the cvc5 SMT solver.
//!
//! For each function signature `f : Domain -> Range` with body `f(x, ...) = expr`,
//! we ask cvc5 to refute:
//!   ∃ params satisfying Domain. expr(params) ∉ Range
//!
//! UNSAT → proved for all inputs. SAT → counterexample returned.
//!
//! **Interprocedural checking (contract-based / modular)**
//! When the body contains a call `g(args)`, we do NOT inline `g`'s body.
//! Instead, for each of `g`'s signatures `g : A -> B` we assert:
//!   args ∈ A  →  result_of_call ∈ B
//! The solver reasons about `result_of_call` only through these contracts.
//! This handles recursion correctly (own signature = induction hypothesis)
//! and respects the library-boundary compilation model (§7).
//!
//! Current limitations (lifted as the language grows):
//! - Only `= expr` (pure) bodies; `{ block }` bodies return `Unknown`.
//! - Only named built-in sets as domain/range (`Int`, `Nat`, `NatPos`, `NonZeroInt`, `IntN`).
//! - Only integer-sorted parameters and return values.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{BinOp, ConstDef, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item, Stmt, UnOp, collect_loop_modified},
    error::CompileError,
    span::{Span, Symbol},
};

// ── Public types ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
pub enum CheckResult {
    /// Every input satisfying the domain maps to an output in the range,
    /// and no built-in operation can produce undefined behaviour.
    Proved,
    /// The solver found concrete parameter values that violate a safety
    /// obligation.  `reason` is a human-readable explanation such as
    /// `"not in Nat"` (range violation) or `"division by zero"`.
    Counterexample { params: HashMap<String, i64>, output: i64, reason: String },
    /// Could not determine (unsupported construct, solver timeout, etc.).
    Unknown(String),
}

/// Map from function name to its definition — used for interprocedural checking.
type FunctionEnv<'a> = HashMap<Symbol, &'a FunctionDef>;

/// Map from constant name to its value expression — used for inlining constants
/// in `encode_expr` when a `Var` reference resolves to a constant, not a param.
type ConstDefs<'a> = HashMap<Symbol, &'a Expr>;

// ── Public entry points ───────────────────────────────────────────────────────

/// Check every function in a parsed file, using each function's signature as
/// a contract available to all other functions in the file.
///
/// Returns one entry per function, each containing one result per signature.
pub fn check_file(items: &[Item]) -> Result<Vec<(String, Vec<(String, CheckResult)>)>, CompileError> {
    let fn_env: FunctionEnv<'_> = items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => Some((def.name.clone(), def)),
            Item::ConstDef(_) => None,
        })
        .collect();

    let const_defs: ConstDefs<'_> = items
        .iter()
        .filter_map(|item| match item {
            Item::ConstDef(def) => Some((def.name.clone(), &def.value)),
            Item::FunctionDef(_) => None,
        })
        .collect();

    items
        .iter()
        .map(|item| match item {
            Item::FunctionDef(def) => {
                let results = check_function(def, &fn_env, &const_defs)?;
                Ok((def.name.0.clone(), results))
            }
            Item::ConstDef(def) => {
                let result = check_const(def, &fn_env, &const_defs);
                let label = format!("{} : {} = {}", def.name, def.ty, def.value);
                Ok((def.name.0.clone(), vec![(label, result)]))
            }
        })
        .collect()
}

/// Check one function definition against its signatures.
///
/// `fn_env` provides the contracts of all other (and the same) functions
/// reachable from this function's body.
pub fn check_function(
    def: &FunctionDef,
    fn_env: &FunctionEnv<'_>,
    const_defs: &ConstDefs<'_>,
) -> Result<Vec<(String, CheckResult)>, CompileError> {
    let param_names: Vec<Symbol> = def.params.iter().map(|p| p.name.clone()).collect();

    Ok(def
        .sigs
        .iter()
        .enumerate()
        .map(|(i, sig)| {
            let label = sig_label(&def.name.0, i, def.sigs.len());
            let result = match &def.body {
                FunctionBody::Expr(body) => check_sig(sig, &param_names, body, fn_env, const_defs),
                FunctionBody::Block(stmts) => check_block_sig(sig, &param_names, stmts, fn_env, const_defs),
            };
            (label, result)
        })
        .collect())
}

fn sig_label(name: &str, idx: usize, total: usize) -> String {
    if total == 1 {
        name.to_owned()
    } else {
        format!("{name} (sig {})", idx + 1)
    }
}

/// Type-check a constant: verify that `def.value ∈ def.ty`.
fn check_const(def: &ConstDef, fn_env: &FunctionEnv<'_>, const_defs: &ConstDefs<'_>) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA");
    solver.set_option("produce-models", "true");

    let env = Env::new();
    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);

    let value_term = match encode_expr(
        &def.value, &env, const_defs, fn_env, &tm, &mut solver,
        &mut call_counter, &mut builtin_obligs, top_guard,
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    match membership_constraint(&tm, value_term, &def.ty) {
        Membership::Unconstrained => CheckResult::Proved,
        Membership::Constrained(c) => {
            solver.assert_formula(tm.mk_term(Kind::Not, &[c]));
            let sat = solver.check_sat();
            if sat.is_unsat() {
                CheckResult::Proved
            } else if sat.is_sat() {
                CheckResult::Counterexample {
                    params: HashMap::new(),
                    output: 0,
                    reason: format!("constant value not in {}", def.ty),
                }
            } else {
                CheckResult::Unknown("solver returned unknown".into())
            }
        }
        Membership::Unsupported => CheckResult::Unknown("unsupported type annotation".into()),
    }
}

// ── Block body checker ────────────────────────────────────────────────────────

/// True if `stmts` contains a `while` loop at any nesting depth.
///
/// Used to decide whether a SAT result is trustworthy: after loop invalidation,
/// fresh variables for constrained `mut` locals carry their declared invariant,
/// but the inductive step is trusted rather than verified.  A SAT result may
/// therefore be spurious (the invariant could be wrong).  Only UNSAT (Proved)
/// is reliable — it means even with the trusted invariant the obligation holds.
fn body_has_while(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::While { .. } => true,
        Stmt::Block(inner) => body_has_while(inner),
        _ => false,
    })
}

/// Check a `{ stmts }` body against one signature.
///
/// Statements are processed in order with an SSA-style environment: each
/// `mut`/assignment introduces a fresh SMT constant tied to the current value.
/// `assume` adds a fact to the solver; `require` proves the fact first (and
/// returns a counterexample if the proof fails).
fn check_block_sig(
    sig: &FunctionSig,
    param_names: &[Symbol],
    stmts: &[Stmt],
    fn_env: &FunctionEnv<'_>,
    const_defs: &ConstDefs<'_>,
) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA");
    solver.set_option("produce-models", "true");

    let int_sort = tm.integer_sort();

    let domain_parts: Vec<&Expr> = match &sig.domain {
        None => vec![],
        Some(domain_expr) => {
            let parts = flatten_product(domain_expr);
            if parts.len() != param_names.len() {
                return CheckResult::Unknown(format!(
                    "domain arity {} doesn't match parameter count {}",
                    parts.len(),
                    param_names.len()
                ));
            }
            parts
        }
    };

    let param_terms: Vec<Term<'_>> = param_names
        .iter()
        .map(|n| tm.mk_const(int_sort.clone(), &n.0))
        .collect();

    // accumulated_facts: all assertions so far (domain constraints, SSA
    // equalities, assume/proved-require facts).  Replayed in a fresh solver
    // for each `require` check so the check has the full current proof state.
    let mut accumulated_facts: Vec<Term<'_>> = Vec::new();

    for (term, part) in param_terms.iter().zip(domain_parts.iter()) {
        match membership_constraint(&tm, term.clone(), part) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => {
                solver.assert_formula(c.clone());
                accumulated_facts.push(c);
            }
            Membership::Unsupported => {
                return CheckResult::Unknown("unsupported domain set expression".into());
            }
        }
    }

    let mut env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let mut ssa_counter = 0usize;

    let mut constraint_env: HashMap<Symbol, Expr> = HashMap::new();
    let body_term = match encode_block(
        stmts,
        &mut env,
        const_defs,
        fn_env,
        &tm,
        &mut solver,
        &mut call_counter,
        &mut builtin_obligs,
        &mut ssa_counter,
        &mut accumulated_facts,
        param_names,
        &param_terms,
        &mut constraint_env,
    ) {
        Ok(Some(t)) => t,
        Ok(None) => {
            return CheckResult::Unknown("block body has no return expression".into());
        }
        Err(early) => return early,
    };

    // Range + built-in obligations — identical tail to check_sig.
    let range_obligation = match membership_constraint(&tm, body_term.clone(), &sig.range) {
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
                tm.mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
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
        tm.mk_term(Kind::And, &all_obligations)
    };
    solver.assert_formula(tm.mk_term(Kind::Not, &[combined]));

    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        // The loop invariant is trusted, not inductively verified, so a SAT
        // result may be spurious (the invariant might not actually hold after
        // every iteration).  Treat as Unknown; the developer can tighten the
        // constraint or add `assert`/`assume` inside the loop body.
        if body_has_while(stmts) {
            return CheckResult::Unknown(
                "while loop: declare mutable variable constraints (`mut name: Set = expr`) to prove post-loop properties".into()
            );
        }
        let mut cex_params = HashMap::new();
        for (name, term) in param_names.iter().zip(param_terms.iter()) {
            let val = solver.get_value(term.clone());
            cex_params.insert(name.0.clone(), integer_value(&val));
        }
        let reason = builtin_obligs
            .iter()
            .find(|o| {
                boolean_value(&solver.get_value(o.path_cond.clone()))
                    && !boolean_value(&solver.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string())
            .unwrap_or_else(|| format!("not in {}", sig.range));
        let output_term = solver.get_value(body_term);
        CheckResult::Counterexample {
            params: cex_params,
            output: integer_value(&output_term),
            reason,
        }
    } else {
        CheckResult::Unknown("solver returned unknown".into())
    }
}

/// Process a sequence of statements, threading the SSA environment.
///
/// Returns `Ok(Some(term))` where `term` is the last `Stmt::Expr` value,
/// `Ok(None)` if there was no return expression, or `Err(result)` for an
/// early exit (require failure, unsupported construct, etc.).
fn encode_block<'tm>(
    stmts: &[Stmt],
    env: &mut Env<'tm>,
    const_defs: &ConstDefs<'_>,
    fn_env: &FunctionEnv<'_>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    ssa_counter: &mut usize,
    accumulated_facts: &mut Vec<Term<'tm>>,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    constraint_env: &mut HashMap<Symbol, Expr>,
) -> Result<Option<Term<'tm>>, CheckResult> {
    let top_guard = tm.mk_boolean(true);
    let mut last_expr: Option<Term<'tm>> = None;

    for stmt in stmts {
        last_expr = None; // only the last Expr stmt is the return value
        match stmt {
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
                // SSA: bind name to a fresh constant equal to the encoded value.
                let ssa_name = format!("{}_{}", name.0, ssa_counter);
                *ssa_counter += 1;
                let fresh = tm.mk_const(tm.integer_sort(), &ssa_name);
                let eq = tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                solver.assert_formula(eq.clone());
                accumulated_facts.push(eq);
                // If the variable carries a declared invariant, assert it holds
                // for the new value (trusted, used as inductive hypothesis).
                if let Some(constraint) = constraint_env.get(name) {
                    if let Membership::Constrained(c) = membership_constraint(tm, fresh.clone(), constraint) {
                        solver.assert_formula(c.clone());
                        accumulated_facts.push(c);
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
                        // Add the proved fact for subsequent statements.
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
                        // pred is not always true.  Check whether it can EVER be
                        // true (in context of accumulated_facts).  If NOT(pred) is
                        // provable then pred is always false → compile error.
                        // Otherwise pred is sometimes true → runtime check needed.
                        let not_pred = tm.mk_term(Kind::Not, &[pred.clone()]);
                        match check_require(not_pred, tm, accumulated_facts, param_names, param_terms) {
                            CheckResult::Proved => {
                                // NOT(pred) always holds → pred never holds.
                                return Err(CheckResult::Counterexample {
                                    params,
                                    output,
                                    reason: "assertion always fails".to_string(),
                                });
                            }
                            _ => {
                                // pred is sometimes true — codegen emits a runtime
                                // check.  Add as a fact so downstream proofs can
                                // assume the assert passed (the code path where it
                                // didn't pass exits early at runtime).
                                solver.assert_formula(pred.clone());
                                accumulated_facts.push(pred);
                            }
                        }
                    }
                    CheckResult::Unknown(_) => {
                        // Can't determine statically; codegen emits a runtime check.
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
                    constraint_env,
                )?;
            }

            Stmt::While { cond, body, .. } => {
                // Sound conservative approximation: we cannot reason statically
                // about how many iterations execute, so we:
                //   1. Invalidate every variable the loop body assigns by
                //      replacing it with a fresh SMT constant.
                //   2. For variables declared with a constraint (`mut x: Set`),
                //      assert the constraint on the fresh constant — this serves
                //      as the loop invariant (trusted, not yet verified inductively).
                //   3. Assert ¬cond (the loop has exited).
                let modified = collect_loop_modified(body);
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

                // Assert the exit condition: cond is false after the loop.
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
        }
    }

    Ok(last_expr)
}

/// Run a temporary solver query to check whether `obligation` is provable
/// under `accumulated_facts`.  Returns `Proved`, a `Counterexample`, or
/// `Unknown` — never `Proved` for the require-failure path.
fn check_require<'tm>(
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

// ── Core per-signature check ──────────────────────────────────────────────────

fn check_sig(
    sig: &FunctionSig,
    param_names: &[Symbol],
    body: &Expr,
    fn_env: &FunctionEnv<'_>,
    const_defs: &ConstDefs<'_>,
) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA"); // Quantifier-Free Non-linear Integer Arithmetic (superset of QF_LIA)
    solver.set_option("produce-models", "true");

    let int_sort = tm.integer_sort();

    // Flatten domain into one set-expr per parameter.
    let domain_parts: Vec<&Expr> = match &sig.domain {
        None => vec![], // zero-arg function
        Some(domain_expr) => {
            let parts = flatten_product(domain_expr);
            if parts.len() != param_names.len() {
                return CheckResult::Unknown(format!(
                    "domain arity {} doesn't match parameter count {}",
                    parts.len(),
                    param_names.len()
                ));
            }
            parts
        }
    };

    // Declare one unconstrained integer variable per parameter.
    let param_terms: Vec<Term<'_>> = param_names
        .iter()
        .map(|n| tm.mk_const(int_sort.clone(), &n.0))
        .collect();

    // Assert domain membership for each parameter.
    for (term, part) in param_terms.iter().zip(domain_parts.iter()) {
        match membership_constraint(&tm, term.clone(), part) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => solver.assert_formula(c),
            Membership::Unsupported => {
                return CheckResult::Unknown("unsupported domain set expression".into())
            }
        }
    }

    // Build local variable environment: symbol → Term.
    let env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    // Encode the body, collecting built-in argument domain obligations as we go.
    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);
    let body_term = match encode_expr(
        body, &env, const_defs, fn_env, &tm, &mut solver, &mut call_counter,
        &mut builtin_obligs, top_guard,
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    // Range obligation: body_term ∈ sig.range.
    let range_obligation = match membership_constraint(&tm, body_term.clone(), &sig.range) {
        Membership::Unconstrained => None,
        Membership::Constrained(c) => Some(c),
        Membership::Unsupported => {
            return CheckResult::Unknown("unsupported range set expression".into())
        }
    };

    // Built-in argument domain obligations, each guarded by the path condition
    // under which the operation is reachable:  path_cond → obligation.
    let builtin_formulas: Vec<Term<'_>> = builtin_obligs
        .iter()
        .map(|o| {
            if o.path_cond.to_string().trim() == "true" {
                o.obligation.clone()
            } else {
                tm.mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
            }
        })
        .collect();

    // Combine everything, negate, and ask the solver.
    // UNSAT → all obligations always hold → Proved.
    // SAT   → some obligation can be falsified → Counterexample.
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
        tm.mk_term(Kind::And, &all_obligations)
    };
    solver.assert_formula(tm.mk_term(Kind::Not, &[combined]));

    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        let mut cex_params = HashMap::new();
        for (name, term) in param_names.iter().zip(param_terms.iter()) {
            let val = solver.get_value(term.clone());
            cex_params.insert(name.0.clone(), integer_value(&val));
        }

        // Find the first built-in obligation that fails in this model.
        // An obligation fails when its guard holds AND its predicate is false.
        let reason = builtin_obligs
            .iter()
            .find(|o| {
                boolean_value(&solver.get_value(o.path_cond.clone()))
                    && !boolean_value(&solver.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string())
            .unwrap_or_else(|| format!("not in {}", sig.range));

        let output_term = solver.get_value(body_term);
        CheckResult::Counterexample {
            params: cex_params,
            output: integer_value(&output_term),
            reason,
        }
    } else {
        CheckResult::Unknown("solver returned unknown".into())
    }
}

// ── Set membership ────────────────────────────────────────────────────────────

/// The result of asking "what does `t ∈ set_expr` look like as a cvc5 term?"
enum Membership<'tm> {
    /// The set is ℤ — every integer qualifies; no assertion needed.
    Unconstrained,
    /// A concrete cvc5 predicate that holds iff `t` is in the set.
    Constrained(Term<'tm>),
    /// The set expression uses syntax we don't yet encode.
    Unsupported,
}

/// Recursively build a membership predicate for structured set expressions.
///
/// Handles named built-in sets, set literals `{n, …}`, set difference `A - B`,
/// set union `A | B`, and set intersection `A & B`.
fn membership_constraint<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set_expr: &Expr,
) -> Membership<'tm> {
    match &set_expr.kind {
        ExprKind::Var(sym) => match sym.0.as_str() {
            "Int"        => Membership::Unconstrained,
            // Fail is the out-of-band failure sentinel — no integer value is ever
            // in Fail.  Constrained(false) means "this predicate never holds for
            // an integer t", which causes Nat | Fail to simplify to Nat >= 0
            // correctly: (t >= 0) || false = (t >= 0).
            "Fail"       => Membership::Constrained(tm.mk_boolean(false)),
            "Nat"        => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Geq, &[t, zero]))
            }
            "NatPos"     => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Gt, &[t, zero]))
            }
            "NonZeroInt" => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Distinct, &[t, zero]))
            }
            "Int8"   => bounded(tm, t, i8::MIN  as i64, i8::MAX  as i64),
            "Int16"  => bounded(tm, t, i16::MIN as i64, i16::MAX as i64),
            "Int32"  => bounded(tm, t, i32::MIN as i64, i32::MAX as i64),
            "Int64"  => bounded(tm, t, i64::MIN,        i64::MAX        ),
            _ => Membership::Unsupported,
        },

        ExprKind::SetLit(elements) => {
            if elements.is_empty() {
                return Membership::Unsupported; // empty set — caller gets Unknown
            }
            // t ∈ {v₁, v₂, …}  ↔  t == v₁  ∨  t == v₂  ∨  …
            // Only integer literals are supported inside set literals for now.
            let eqs: Option<Vec<Term<'_>>> = elements
                .iter()
                .map(|e| match &e.kind {
                    ExprKind::IntLit(n) => {
                        let n_term = tm.mk_integer(*n);
                        Some(tm.mk_term(Kind::Equal, &[t.clone(), n_term]))
                    }
                    _ => None,
                })
                .collect();

            match eqs {
                None => Membership::Unsupported,
                Some(mut eqs) => {
                    let term = if eqs.len() == 1 {
                        eqs.remove(0)
                    } else {
                        tm.mk_term(Kind::Or, &eqs)
                    };
                    Membership::Constrained(term)
                }
            }
        }

        // `-` in signature position means set difference (A ∖ B).
        ExprKind::BinOp { op: BinOp::Sub, lhs, rhs } => {
            // t ∈ A - B  ↔  (t ∈ A) ∧ ¬(t ∈ B)
            let not_in_b = match membership_constraint(tm, t.clone(), rhs) {
                Membership::Unsupported => return Membership::Unsupported,
                Membership::Unconstrained => {
                    // B is ℤ, so A - B = ∅; nothing is a member.
                    return Membership::Unsupported;
                }
                Membership::Constrained(c) => tm.mk_term(Kind::Not, &[c]),
            };
            match membership_constraint(tm, t, lhs) {
                Membership::Unsupported => Membership::Unsupported,
                Membership::Unconstrained => Membership::Constrained(not_in_b),
                Membership::Constrained(c) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[c, not_in_b]))
                }
            }
        }

        // `|` in signature position means set union.
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            // t ∈ A | B  ↔  (t ∈ A) ∨ (t ∈ B)
            let in_a = membership_constraint(tm, t.clone(), lhs);
            let in_b = membership_constraint(tm, t, rhs);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Membership::Unsupported,
                (Membership::Unconstrained, _) | (_, Membership::Unconstrained) => Membership::Unconstrained,
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::Or, &[a, b]))
                }
            }
        }

        // `&` in signature position means set intersection.
        ExprKind::BinOp { op: BinOp::Intersect, lhs, rhs } => {
            // t ∈ A & B  ↔  (t ∈ A) ∧ (t ∈ B)
            let in_a = membership_constraint(tm, t.clone(), lhs);
            let in_b = membership_constraint(tm, t, rhs);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Membership::Unsupported,
                (Membership::Unconstrained, other) => other,
                (other, Membership::Unconstrained) => other,
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[a, b]))
                }
            }
        }

        _ => Membership::Unsupported,
    }
}

fn bounded<'tm>(tm: &'tm TermManager, t: Term<'tm>, min: i64, max: i64) -> Membership<'tm> {
    let lo  = tm.mk_integer(min);
    let hi  = tm.mk_integer(max);
    let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
    let leq = tm.mk_term(Kind::Leq, &[t, hi]);
    Membership::Constrained(tm.mk_term(Kind::And, &[geq, leq]))
}

// ── Expression encoding ───────────────────────────────────────────────────────

type Env<'tm> = HashMap<Symbol, Term<'tm>>;

// ── Built-in operator domain table ───────────────────────────────────────────

/// A proof obligation produced when encoding a built-in operator argument.
///
/// `check_sig` asserts `path_cond → obligation` and, on a SAT result,
/// inspects the model to report `violated_reason` in the counterexample.
struct BuiltinObligation<'tm> {
    path_cond: Term<'tm>,
    obligation: Term<'tm>,
    violated_reason: &'static str,
}

/// Domain constraint for argument `arg_idx` (0-based) of a binary built-in,
/// expressed as a named Cantor set + a human-readable violation reason.
///
/// This is the authoritative table of every binary operator's argument types.
/// `None` means the argument is unconstrained (accepts any `Int`).
/// When `Bool` is added as a type, `And`/`Or` rows will appear here.
fn binary_builtin_domain(op: &BinOp, arg_idx: usize) -> Option<(Expr, &'static str)> {
    match (op, arg_idx) {
        (BinOp::Div, 1) => Some((named_set("NonZeroInt"), "division by zero")),
        _ => None,
    }
}

/// Domain constraint for the operand of a unary built-in.
///
/// `None` means unconstrained.  `Not` will reference `Bool` once that type
/// is visible to the solver.
fn unary_builtin_domain(op: &UnOp) -> Option<(Expr, &'static str)> {
    match op {
        UnOp::Neg => None, // Int -> Int
        UnOp::Not => None, // Bool -> Bool (Bool not yet a solver-visible type)
    }
}

/// Build a `Var` expression that refers to a named built-in set.
fn named_set(name: &'static str) -> Expr {
    Expr::new(ExprKind::Var(Symbol::new(name)), Span::dummy())
}

// ── Expression encoder ────────────────────────────────────────────────────────

/// Recursively encode a Cantor expression as a cvc5 `Term`.
///
/// When a function call is encountered, a fresh integer variable is introduced
/// for the return value, and the callee's per-signature contracts are asserted
/// as implications: `args ∈ domain → result ∈ range`.
///
/// `path_cond` is the conjunction of all branch conditions required to reach
/// this point in the expression.  `builtin_obligs` accumulates one entry per
/// built-in operator argument that has a domain constraint; `check_sig` then
/// asserts `path_cond → obligation` for each, giving fully path-sensitive
/// safety checking for every built-in.
fn encode_expr<'tm>(
    expr: &Expr,
    env: &Env<'tm>,
    const_defs: &ConstDefs<'_>,
    fn_env: &FunctionEnv<'_>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    path_cond: Term<'tm>,
) -> Result<Term<'tm>, String> {
    // Convenience: recurse with the same path condition.
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, const_defs, fn_env, tm, solver, call_counter, builtin_obligs, path_cond.clone())
        };
    }

    match &expr.kind {
        ExprKind::IntLit(n) => Ok(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Ok(tm.mk_boolean(*b)),

        ExprKind::Var(sym) => {
            if let Some(term) = env.get(sym) {
                Ok(term.clone())
            } else if let Some(const_expr) = const_defs.get(sym) {
                // Inline the constant's value expression (no params, same const_defs
                // so chained constants like `tau = 2 * pi` resolve correctly).
                encode_expr(const_expr, &Env::new(), const_defs, fn_env, tm, solver,
                            call_counter, builtin_obligs, path_cond)
            } else {
                Err(format!("unbound variable `{}`", sym.0))
            }
        }

        ExprKind::UnOp { op, expr: inner } => {
            let t = enc!(inner)?;
            if let Some((domain, reason)) = unary_builtin_domain(op) {
                if let Membership::Constrained(c) = membership_constraint(tm, t.clone(), &domain) {
                    builtin_obligs.push(BuiltinObligation {
                        path_cond: path_cond.clone(),
                        obligation: c,
                        violated_reason: reason,
                    });
                }
            }
            match op {
                UnOp::Neg => Ok(tm.mk_term(Kind::Neg, &[t])),
                UnOp::Not => Ok(tm.mk_term(Kind::Not, &[t])),
            }
        }

        ExprKind::BinOp { op, lhs, rhs } => {
            // `x in S` and `x not in S` are boolean membership predicates.
            // Handle them before encoding both sides, since the RHS is a set
            // expression (not an integer term) and would fail normal encoding.
            match op {
                BinOp::In => {
                    let l = enc!(lhs)?;
                    return match membership_constraint(tm, l, rhs) {
                        Membership::Constrained(c)  => Ok(c),
                        Membership::Unconstrained    => Ok(tm.mk_boolean(true)),
                        Membership::Unsupported      => Err("unsupported set in `in` expression".into()),
                    };
                }
                BinOp::NotIn => {
                    let l = enc!(lhs)?;
                    return match membership_constraint(tm, l, rhs) {
                        Membership::Constrained(c)  => Ok(tm.mk_term(Kind::Not, &[c])),
                        Membership::Unconstrained    => Ok(tm.mk_boolean(false)),
                        Membership::Unsupported      => Err("unsupported set in `not in` expression".into()),
                    };
                }
                _ => {}
            }

            let l = enc!(lhs)?;
            let r = enc!(rhs)?;

            // Check each argument against the operator's declared domain.
            for (arg_idx, arg_term) in [&l, &r].iter().enumerate() {
                if let Some((domain, reason)) = binary_builtin_domain(op, arg_idx) {
                    if let Membership::Constrained(c) = membership_constraint(tm, (*arg_term).clone(), &domain) {
                        builtin_obligs.push(BuiltinObligation {
                            path_cond: path_cond.clone(),
                            obligation: c,
                            violated_reason: reason,
                        });
                    }
                }
            }

            let kind = match op {
                BinOp::Add => Kind::Add,
                BinOp::Sub => Kind::Sub,
                BinOp::Mul => Kind::Mult,
                BinOp::Div => Kind::IntsDivision,
                BinOp::Eq  => Kind::Equal,
                BinOp::Ne  => Kind::Distinct,
                BinOp::Lt  => Kind::Lt,
                BinOp::Le  => Kind::Leq,
                BinOp::Gt  => Kind::Gt,
                BinOp::Ge  => Kind::Geq,
                BinOp::And => Kind::And,
                BinOp::Or  => Kind::Or,
                BinOp::In | BinOp::NotIn => unreachable!("handled above"),
                BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
                    return Err(format!("set operation `{op:?}` not yet encodable"))
                }
            };
            Ok(tm.mk_term(kind, &[l, r]))
        }

        ExprKind::If { cond, then_expr, else_expr } => {
            // The condition is evaluated on the current path.
            let c = enc!(cond)?;

            // Then-branch: path_cond ∧ cond
            let then_guard = tm.mk_term(Kind::And, &[path_cond.clone(), c.clone()]);
            let t = encode_expr(
                then_expr, env, const_defs, fn_env, tm, solver, call_counter, builtin_obligs, then_guard,
            )?;

            // Else-branch: path_cond ∧ ¬cond
            let not_c = tm.mk_term(Kind::Not, &[c.clone()]);
            let else_guard = tm.mk_term(Kind::And, &[path_cond, not_c]);
            let e = encode_expr(
                else_expr, env, const_defs, fn_env, tm, solver, call_counter, builtin_obligs, else_guard,
            )?;

            Ok(tm.mk_term(Kind::Ite, &[c, t, e]))
        }

        ExprKind::Call { callee, args } => {
            let arg_terms: Vec<Term<'_>> = args
                .iter()
                .map(|a| enc!(a))
                .collect::<Result<_, _>>()?;

            // Look up the callee in the function environment.
            let callee_def = fn_env
                .get(callee)
                .ok_or_else(|| format!("unknown function `{}`", callee.0))?;

            // Fresh unconstrained integer variable for the return value.
            let fresh = format!("_call_{}", *call_counter);
            *call_counter += 1;
            let result_var = tm.mk_const(tm.integer_sort(), &fresh);

            // For each of the callee's signatures, assert the implication:
            //   args ∈ domain  →  result_var ∈ range
            for sig in &callee_def.sigs {
                assert_call_contract(
                    sig,
                    &arg_terms,
                    result_var.clone(),
                    tm,
                    solver,
                );
            }

            Ok(result_var)
        }

        ExprKind::SetLit(_) => {
            Err("set literals cannot appear in function bodies".into())
        }

        // At the SMT level `?` is transparent: we reason only about the success
        // path, so the callee's contract (domain → range) already constrains the
        // result variable.  Runtime failure propagation is a codegen concern.
        //
        // This holds cleanly because `Fail` contributes Constrained(false) —
        // no integer is in it — so the callee's contract is purely about the
        // success type T.  When named error sets (e.g. `T | HTTPError`) are
        // added, they carry real integer constraints, weakening the contract to
        // `T | HTTPError`.  The fix is a tagged-union ABI: value and error live
        // in separate fields so the SMT for the value field stays `∈ T` and
        // `?` remains transparent.  Until then, named error sets will require
        // a narrowing fact `_call_0 ∉ E` to be added here after propagation.
        ExprKind::Try(inner) => enc!(inner),
    }
}

/// Assert `args ∈ domain → result ∈ range` for one callee signature.
///
/// If any part of the domain or range is unsupported, the implication is
/// silently skipped — the solver has less information but never incorrect info.
fn assert_call_contract<'tm>(
    sig: &FunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
) {
    // Build the antecedent: per-arg domain constraints (unconstrained args skipped).
    let mut antecedents: Vec<Term<'_>> = Vec::new();
    match &sig.domain {
        None => {} // zero-arg callee
        Some(domain_expr) => {
            let parts = flatten_product(domain_expr);
            if parts.len() != arg_terms.len() {
                return; // arity mismatch — skip
            }
            for (part, arg) in parts.iter().zip(arg_terms.iter()) {
                match membership_constraint(tm, arg.clone(), part) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => antecedents.push(c),
                    Membership::Unsupported => return, // unsupported domain — skip sig
                }
            }
        }
    }

    // Build the consequent: result ∈ range.
    let consequent = match membership_constraint(tm, result, &sig.range) {
        Membership::Unconstrained => return, // range is `Int` — trivially true
        Membership::Constrained(c) => c,
        Membership::Unsupported => return, // unsupported range — skip sig
    };

    // Combine into an implication (or bare consequent if domain is unconstrained).
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

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Flatten a left-associative `A * B * C` product into `[A, B, C]`.
fn flatten_product(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs } => {
            let mut parts = flatten_product(lhs);
            parts.push(rhs);
            parts
        }
        _ => vec![expr],
    }
}

/// Extract an i64 from a cvc5 integer model term.
fn integer_value(term: &Term<'_>) -> i64 {
    if term.is_int32_value() {
        term.int32_value() as i64
    } else if term.is_int64_value() {
        term.int64_value()
    } else {
        term.to_string().trim().parse::<i64>().unwrap_or(0)
    }
}

/// Extract a bool from a cvc5 boolean model term.
fn boolean_value(term: &Term<'_>) -> bool {
    term.to_string().trim() == "true"
}
