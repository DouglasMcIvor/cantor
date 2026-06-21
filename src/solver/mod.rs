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
//! - Only named built-in sets as domain/range (`Int`, `Nat`, `NatPos`, `NonZeroInt`, `IntN`).
//! - Only integer-sorted parameters and return values.

mod membership;
mod encode;
mod loops;

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item, NameDef},
    span::Symbol,
};

use crate::kind::{Kind as ValKind, set_kind};

use self::encode::{Env, BuiltinObligation, encode_expr, flatten_product, integer_value, boolean_value};
use self::loops::{encode_block, body_has_unconstrained_loop_var};
use self::membership::{Membership, membership_constraint};

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

type FunctionEnv<'a> = HashMap<Symbol, &'a FunctionDef>;
pub(crate) type NameDefs<'a> = HashMap<Symbol, &'a NameDef>;

// ── Public entry points ───────────────────────────────────────────────────────

/// Check every function in a parsed file, using each function's signature as
/// a contract available to all other functions in the file.
///
/// Returns one entry per function, each containing one result per signature.
pub fn check_file(items: &[Item]) -> Result<Vec<(String, Vec<(String, CheckResult)>)>, crate::error::CompileError> {
    let fn_env: FunctionEnv<'_> = items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => Some((def.name.clone(), def)),
            _ => None,
        })
        .collect();

    let name_defs: NameDefs<'_> = items
        .iter()
        .filter_map(|item| match item {
            Item::NameDef(def) => Some((def.name.clone(), def)),
            _ => None,
        })
        .collect();

    items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => {
                let results = check_function(def, &fn_env, &name_defs);
                Some(results.map(|r| (def.name.0.clone(), r)))
            }
            Item::NameDef(def) => {
                // Only annotated defs (`name : Set = value`) produce a check result.
                let ty = def.ty.as_ref()?;
                let result = check_name_def(def, ty, &fn_env, &name_defs);
                let label = format!("{} : {} = {}", def.name, ty, def.value);
                Some(Ok((def.name.0.clone(), vec![(label, result)])))
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
    name_defs: &NameDefs<'_>,
) -> Result<Vec<(String, CheckResult)>, crate::error::CompileError> {
    let param_names: Vec<Symbol> = def.params.iter().map(|p| p.name.clone()).collect();

    Ok(def
        .sigs
        .iter()
        .enumerate()
        .map(|(i, sig)| {
            let label = sig_label(&def.name.0, i, def.sigs.len());
            let result = match &def.body {
                FunctionBody::Expr(body) => check_sig(sig, &param_names, body, fn_env, name_defs),
                FunctionBody::Block(stmts) => check_block_sig(sig, &param_names, stmts, fn_env, name_defs),
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

fn check_name_def(def: &NameDef, ty: &Expr, fn_env: &FunctionEnv<'_>, name_defs: &NameDefs<'_>) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA");
    solver.set_option("produce-models", "true");

    let env = Env::new();
    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);

    let value_term = match encode_expr(
        &def.value, &env, name_defs, fn_env, &tm, &mut solver,
        &mut call_counter, &mut builtin_obligs, top_guard,
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    match membership_constraint(&tm, value_term, ty, name_defs) {
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
                    reason: format!("constant value not in {}", ty),
                }
            } else {
                CheckResult::Unknown("solver returned unknown".into())
            }
        }
        Membership::Unsupported => CheckResult::Unknown("unsupported type annotation".into()),
    }
}

fn range_contains_fail(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::Var(sym) => sym.0 == "Fail",
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            range_contains_fail(lhs) || range_contains_fail(rhs)
        }
        // `A !! B` — always permits runtime failure (the `!!` encodes it as an offset value).
        ExprKind::BinOp { op: BinOp::ErrorUnion, .. } => true,
        _ => false,
    }
}

// ── Block body checker ────────────────────────────────────────────────────────

fn check_block_sig(
    sig: &FunctionSig,
    param_names: &[Symbol],
    stmts: &[crate::ast::Stmt],
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs<'_>,
) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA");
    solver.set_option("produce-models", "true");

    let int_sort  = tm.integer_sort();
    let bool_sort = tm.boolean_sort();

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
        .zip(domain_parts.iter().map(|p| set_kind(p)).chain(std::iter::repeat(ValKind::Int)))
        .map(|(n, k)| {
            if k == ValKind::Bool {
                tm.mk_const(bool_sort.clone(), &n.0)
            } else {
                tm.mk_const(int_sort.clone(), &n.0)
            }
        })
        .take(param_names.len())
        .collect();

    let mut accumulated_facts: Vec<Term<'_>> = Vec::new();

    for (term, part) in param_terms.iter().zip(domain_parts.iter()) {
        if set_kind(part) == ValKind::Bool { continue; }
        match membership_constraint(&tm, term.clone(), part, name_defs) {
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
    let mut has_runtime_assert = false;
    let mut immutable_names: HashSet<Symbol> = HashSet::new();

    let body_term = match encode_block(
        stmts,
        &mut env,
        name_defs,
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
        &mut has_runtime_assert,
        &mut immutable_names,
    ) {
        Ok(Some(t)) => t,
        Ok(None) => {
            return CheckResult::Unknown("block body has no return expression".into());
        }
        Err(early) => return early,
    };

    if has_runtime_assert && !range_contains_fail(&sig.range) {
        return CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: "assert may fail at runtime but return type does not include `Fail` \
                     — add `| Fail` or use `!!` on the return type, or prove the assertion statically"
                .into(),
        };
    }

    let range_obligation = match membership_constraint(&tm, body_term.clone(), &sig.range, name_defs) {
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
        if body_has_unconstrained_loop_var(stmts, &constraint_env, &tm, name_defs) {
            return CheckResult::Unknown(
                "while loop: declare all mutable variable constraints \
                 (`mut name: Set = expr`) to enable counterexample extraction".into()
            );
        }
        let mut cex_params = HashMap::new();
        for (name, term, part) in param_names.iter()
            .zip(param_terms.iter())
            .zip(domain_parts.iter())
            .map(|((n, t), p)| (n, t, p))
        {
            let val = solver.get_value(term.clone());
            let n = if set_kind(part) == ValKind::Bool {
                boolean_value(&val) as i64
            } else {
                integer_value(&val)
            };
            cex_params.insert(name.0.clone(), n);
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

// ── Pure expression body checker ──────────────────────────────────────────────

fn check_sig(
    sig: &FunctionSig,
    param_names: &[Symbol],
    body: &Expr,
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs<'_>,
) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA");
    solver.set_option("produce-models", "true");

    let int_sort  = tm.integer_sort();
    let bool_sort = tm.boolean_sort();

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

    // Create each param constant in the sort that matches its domain Kind.
    // Bool-domain params use the boolean sort so `not b`, `b and c`, etc. work
    // without sort mismatches; integer-domain params use the integer sort.
    let param_terms: Vec<Term<'_>> = param_names
        .iter()
        .zip(domain_parts.iter().map(|p| set_kind(p)).chain(std::iter::repeat(ValKind::Int)))
        .map(|(n, k)| {
            if k == ValKind::Bool {
                tm.mk_const(bool_sort.clone(), &n.0)
            } else {
                tm.mk_const(int_sort.clone(), &n.0)
            }
        })
        .take(param_names.len())
        .collect();

    // Assert domain membership for integer-domain params.
    // Bool-domain params are already constrained by their sort; skip them.
    for (term, part) in param_terms.iter().zip(domain_parts.iter()) {
        if set_kind(part) == ValKind::Bool { continue; }
        match membership_constraint(&tm, term.clone(), part, name_defs) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => solver.assert_formula(c),
            Membership::Unsupported => {
                return CheckResult::Unknown("unsupported domain set expression".into())
            }
        }
    }

    let env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);
    let body_term = match encode_expr(
        body, &env, name_defs, fn_env, &tm, &mut solver, &mut call_counter,
        &mut builtin_obligs, top_guard,
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let range_obligation = match membership_constraint(&tm, body_term.clone(), &sig.range, name_defs) {
        Membership::Unconstrained => None,
        Membership::Constrained(c) => Some(c),
        Membership::Unsupported => {
            return CheckResult::Unknown("unsupported range set expression".into())
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
        let mut cex_params = HashMap::new();
        for (name, term, part) in param_names.iter()
            .zip(param_terms.iter())
            .zip(domain_parts.iter())
            .map(|((n, t), p)| (n, t, p))
        {
            let val = solver.get_value(term.clone());
            let n = if set_kind(part) == ValKind::Bool {
                boolean_value(&val) as i64
            } else {
                integer_value(&val)
            };
            cex_params.insert(name.0.clone(), n);
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
