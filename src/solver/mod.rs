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

mod blocks;
mod encode;
mod loops;
mod membership;
mod sort;

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{BinOp, DefKind, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item, NameDef, param_set_exprs},
    span::Symbol,
};
pub(crate) use crate::ast::NameDefs;

use crate::kind::{Kind as ValKind, set_kind};

use self::encode::{Env, BuiltinObligation, encode_expr, integer_value, boolean_value, mk_decomposed_tuple};
use self::sort::{set_sort, set_sort_for_range};
use self::blocks::{encode_block, body_has_unconstrained_loop_var};
use self::membership::{DistinctInfo, DistinctPreds, Membership, membership_constraint};

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

// ── Distinct predicate builder ────────────────────────────────────────────────

/// For each `D = distinct B` in `name_defs`, create a CVC5 uninterpreted sort plus
/// constructor/destructor uninterpreted functions:
///   - `sort  = mk_uninterpreted_sort("D")`
///   - `mk_D  : Int → D_sort`  (wraps an integer as a D-value)
///   - `from_D: D_sort → Int`  (extracts the underlying integer)
///
/// No global axioms are needed; basis constraints are emitted on-demand when
/// `litre(n)` or `from(x)` is encoded.
fn build_distinct_preds<'tm>(tm: &'tm TermManager, name_defs: &NameDefs) -> DistinctPreds<'tm> {
    name_defs.iter()
        .filter(|(_, def)| def.kind == DefKind::Distinct)
        .map(|(sym, _)| {
            let sort = tm.mk_uninterpreted_sort(&sym.0);
            let mk = tm.mk_const(
                tm.mk_fun_sort(&[tm.integer_sort()], sort.clone()),
                &format!("mk_{}", sym.0),
            );
            let from = tm.mk_const(
                tm.mk_fun_sort(&[sort.clone()], tm.integer_sort()),
                &format!("from_{}", sym.0),
            );
            (sym.clone(), DistinctInfo { sort, mk, from })
        })
        .collect()
}

// ── Public entry points ───────────────────────────────────────────────────────

/// Check every function in a parsed file, using each function's signature as
/// a contract available to all other functions in the file.
///
/// Returns one entry per function, each containing one result per signature.
///
/// `timeout_ms` is applied as the `tlimit` option on every fresh solver
/// instance.  Pass `0` to disable the limit entirely.
pub fn check_file(items: &[Item], timeout_ms: u64) -> Result<Vec<(String, Vec<(String, CheckResult)>)>, crate::error::CompileError> {
    let fn_env: FunctionEnv<'_> = items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => Some((def.name.clone(), def)),
            _ => None,
        })
        .collect();

    let name_defs: NameDefs = items
        .iter()
        .filter_map(|item| match item {
            Item::NameDef(def) => Some((def.name.clone(), def.clone())),
            _ => None,
        })
        .collect();

    items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => {
                let results = check_function(def, &fn_env, &name_defs, timeout_ms);
                Some(results.map(|r| (def.name.0.clone(), r)))
            }
            Item::NameDef(def) => {
                // Only annotated defs (`name : Set = value`) produce a check result.
                let ty = def.ty.as_ref()?;
                let result = check_name_def(def, ty, &fn_env, &name_defs, timeout_ms);
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
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Result<Vec<(String, CheckResult)>, crate::error::CompileError> {
    let param_names: Vec<Symbol> = def.params.iter().map(|p| p.name.clone()).collect();

    Ok(def
        .sigs
        .iter()
        .enumerate()
        .map(|(i, sig)| {
            let label = sig_label(&def.name.0, i, def.sigs.len());
            let result = match &def.body {
                FunctionBody::Expr(body) => check_sig(sig, &param_names, body, fn_env, name_defs, timeout_ms),
                FunctionBody::Block(stmts) => check_block_sig(sig, &param_names, stmts, fn_env, name_defs, timeout_ms),
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

fn check_name_def(def: &NameDef, ty: &Expr, fn_env: &FunctionEnv<'_>, name_defs: &NameDefs, timeout_ms: u64) -> CheckResult {
    if let Some(result) = validate_disjoint_unions(ty, name_defs, timeout_ms) { return result; }
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }

    let distinct_preds = build_distinct_preds(&tm, name_defs);
    let env = Env::new();
    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);

    let value_term = match encode_expr(
        &def.value, &env, name_defs, fn_env, &tm, &mut solver,
        &mut call_counter, &mut builtin_obligs, top_guard, &distinct_preds, None,
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    match membership_constraint(&tm, value_term, ty, name_defs, &distinct_preds) {
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
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            range_contains_fail(lhs) || range_contains_fail(rhs)
        }
        // `Fail * Y` — desugared from `!! Y`; always a failure arm.
        ExprKind::BinOp { op: BinOp::Mul, lhs, .. } => {
            matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
        }
        _ => false,
    }
}

/// Verify that every `+` (disjoint union) in `set_expr` has genuinely disjoint operands.
///
/// Returns `Some(CheckResult)` on failure or `None` if all `+` nodes are proved disjoint.
/// Uses a fresh SMT solver per `+` node to avoid polluting the main check's solver state.
///
/// TODO: also validate `+` that appears inside function bodies (e.g. in `in` expressions).
fn validate_disjoint_unions(set_expr: &Expr, name_defs: &NameDefs, timeout_ms: u64) -> Option<CheckResult> {
    match &set_expr.kind {
        ExprKind::BinOp { op: BinOp::Add, lhs, rhs } => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) { return Some(err); }
            if let Some(err) = validate_disjoint_unions(rhs, name_defs, timeout_ms) { return Some(err); }

            let tm = TermManager::new();
            let mut solver = Solver::new(&tm);
            solver.set_logic("ALL");
            if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }
            let distinct_preds = build_distinct_preds(&tm, name_defs);
            let t = tm.mk_const(tm.integer_sort(), "__disjoint_check");
            let in_a = membership_constraint(&tm, t.clone(), lhs, name_defs, &distinct_preds);
            let in_b = membership_constraint(&tm, t, rhs, name_defs, &distinct_preds);

            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Some(
                    CheckResult::Unknown(format!("cannot verify disjointness of `{lhs}` and `{rhs}`"))
                ),
                (ca, cb) => {
                    if let Membership::Constrained(c) = ca { solver.assert_formula(c); }
                    if let Membership::Constrained(c) = cb { solver.assert_formula(c); }
                    let sat = solver.check_sat();
                    if sat.is_unsat() {
                        None // proved disjoint
                    } else if sat.is_sat() {
                        Some(CheckResult::Counterexample {
                            params: HashMap::new(),
                            output: 0,
                            reason: format!(
                                "`{lhs}` and `{rhs}` are not disjoint \
                                 — `+` requires disjoint sets; use `|` for plain union"
                            ),
                        })
                    } else {
                        Some(CheckResult::Unknown(format!(
                            "cannot prove `{lhs}` and `{rhs}` are disjoint"
                        )))
                    }
                }
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) { return Some(err); }
            validate_disjoint_unions(rhs, name_defs, timeout_ms)
        }
        ExprKind::Call { args, .. } => {
            for arg in args {
                if let Some(err) = validate_disjoint_unions(arg, name_defs, timeout_ms) { return Some(err); }
            }
            None
        }
        _ => None,
    }
}

// ── Block body checker ────────────────────────────────────────────────────────

fn check_block_sig(
    sig: &FunctionSig,
    param_names: &[Symbol],
    stmts: &[crate::ast::Stmt],
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> CheckResult {
    if let Some(dom) = &sig.domain {
        if let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms) { return result; }
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) { return result; }

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }

    let distinct_preds = build_distinct_preds(&tm, name_defs);

    let domain_parts: Vec<&Expr> = match param_set_exprs(sig.domain.as_ref(), param_names.len()) {
        Ok(parts) => parts,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let mut accumulated_facts: Vec<Term<'_>> = Vec::new();

    // Same decomposition as check_sig: tuple params → leaf constants + mk_tuple.
    let mut param_terms: Vec<Term<'_>> = Vec::new();
    for (n, part) in param_names.iter().zip(domain_parts.iter()) {
        let k = set_kind(part, &name_defs);
        if matches!(k, ValKind::Tuple(_)) {
            let (assembled, leaves) = mk_decomposed_tuple(&tm, &n.0, part, &distinct_preds, &name_defs);
            for (leaf, leaf_set) in leaves {
                match membership_constraint(&tm, leaf.clone(), leaf_set, name_defs, &distinct_preds) {
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
            param_terms.push(assembled);
        } else {
            let sort = match set_sort(&tm, part, &distinct_preds, &name_defs) {
                Some(s) => s,
                None => return CheckResult::Unknown(format!(
                    "parameter `{}` has an unsupported domain sort (internal error)",
                    n.0
                )),
            };
            let term = tm.mk_const(sort, &n.0);
            if k != ValKind::Bool {
                match membership_constraint(&tm, term.clone(), part, name_defs, &distinct_preds) {
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
            param_terms.push(term);
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

    let result_sort = set_sort_for_range(&tm, &sig.range, &distinct_preds, &name_defs);
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
        &distinct_preds,
        result_sort,
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

    let range_obligation = match membership_constraint(&tm, body_term.clone(), &sig.range, name_defs, &distinct_preds) {
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
        if body_has_unconstrained_loop_var(stmts, &constraint_env, &tm, name_defs, &distinct_preds) {
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
            let k = set_kind(part, &name_defs);
            let n = if k == ValKind::Bool {
                boolean_value(&val) as i64
            } else if matches!(k, ValKind::Tuple(_)) {
                0 // TODO: render tuple model value in counterexample display
            } else if matches!(k, ValKind::TaggedUnion(_)) {
                0 // TODO: decode datatype arm for cross-kind union counterexample display
            } else if matches!(k, ValKind::Vector(_)) {
                0 // TODO: render vector model value in counterexample display
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
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> CheckResult {
    if let Some(dom) = &sig.domain {
        if let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms) { return result; }
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) { return result; }

    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence-theory goals use universally-quantified membership constraints.
    // `full-saturate-quant` tells cvc5 to keep instantiating quantifiers until
    // a model is found — needed to produce counterexamples for ¬(∀i. …) goals.
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }

    let distinct_preds = build_distinct_preds(&tm, name_defs);

    // param_set_exprs guarantees domain_parts.len() == param_names.len() on Ok.
    let domain_parts: Vec<&Expr> = match param_set_exprs(sig.domain.as_ref(), param_names.len()) {
        Ok(parts) => parts,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    // Create each param constant.  For tuple params, decompose into leaf scalar
    // constants assembled with mk_tuple — this ensures TupleProject in the body
    // always operates on a concrete mk_tuple term (not a symbolic tuple constant),
    // which is required for cvc5's arithmetic beta-reduction to apply.
    let mut param_terms: Vec<Term<'_>> = Vec::new();
    for (n, part) in param_names.iter().zip(domain_parts.iter()) {
        let k = set_kind(part, &name_defs);
        if matches!(k, ValKind::Tuple(_)) {
            let (assembled, leaves) = mk_decomposed_tuple(&tm, &n.0, part, &distinct_preds, &name_defs);
            for (leaf, leaf_set) in leaves {
                match membership_constraint(&tm, leaf, leaf_set, name_defs, &distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return CheckResult::Unknown("unsupported domain set expression".into())
                    }
                }
            }
            param_terms.push(assembled);
        } else {
            let sort = match set_sort(&tm, part, &distinct_preds, &name_defs) {
                Some(s) => s,
                None => return CheckResult::Unknown(format!(
                    "parameter `{}` has an unsupported domain sort (internal error)",
                    n.0
                )),
            };
            let term = tm.mk_const(sort, &n.0);
            if k != ValKind::Bool {
                match membership_constraint(&tm, term.clone(), part, name_defs, &distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return CheckResult::Unknown("unsupported domain set expression".into())
                    }
                }
            }
            param_terms.push(term);
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
        &mut builtin_obligs, top_guard, &distinct_preds, set_sort_for_range(&tm, &sig.range, &distinct_preds, &name_defs),
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let range_obligation = match membership_constraint(&tm, body_term.clone(), &sig.range, name_defs, &distinct_preds) {
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
            let k = set_kind(part, &name_defs);
            let n = if k == ValKind::Bool {
                boolean_value(&val) as i64
            } else if matches!(k, ValKind::Tuple(_)) {
                0 // TODO: render tuple model value in counterexample display
            } else if matches!(k, ValKind::TaggedUnion(_)) {
                0 // TODO: decode datatype arm for cross-kind union counterexample display
            } else if matches!(k, ValKind::Vector(_)) {
                0 // TODO: render vector model value in counterexample display
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
