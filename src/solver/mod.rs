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
//! - Only named built-in sets as domain/range (`Int`, `Nat`, `NatPos`, `IntN`).
//! - Only integer-sorted parameters and return values.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item, UnOp},
    error::CompileError,
    span::Symbol,
};

// ── Public types ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
pub enum CheckResult {
    /// Every input satisfying the domain maps to an output in the range.
    Proved,
    /// The solver found concrete parameter values that violate the range.
    Counterexample { params: HashMap<String, i64>, output: i64 },
    /// Could not determine (unsupported construct, solver timeout, etc.).
    Unknown(String),
}

/// Map from function name to its definition — used for interprocedural checking.
type FunctionEnv<'a> = HashMap<Symbol, &'a FunctionDef>;

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
        })
        .collect();

    items
        .iter()
        .map(|item| match item {
            Item::FunctionDef(def) => {
                let results = check_function(def, &fn_env)?;
                Ok((def.name.0.clone(), results))
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
) -> Result<Vec<(String, CheckResult)>, CompileError> {
    let body_expr = match &def.body {
        FunctionBody::Expr(e) => e,
        FunctionBody::Block(_) => {
            return Ok(def
                .sigs
                .iter()
                .enumerate()
                .map(|(i, _)| {
                    (
                        sig_label(&def.name.0, i, def.sigs.len()),
                        CheckResult::Unknown("block bodies are not yet checked".into()),
                    )
                })
                .collect())
        }
    };

    let param_names: Vec<Symbol> = def.params.iter().map(|p| p.name.clone()).collect();

    Ok(def
        .sigs
        .iter()
        .enumerate()
        .map(|(i, sig)| {
            let label = sig_label(&def.name.0, i, def.sigs.len());
            let result = check_sig(sig, &param_names, body_expr, fn_env);
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

// ── Core per-signature check ──────────────────────────────────────────────────

fn check_sig(
    sig: &FunctionSig,
    param_names: &[Symbol],
    body: &Expr,
    fn_env: &FunctionEnv<'_>,
) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_NIA"); // Quantifier-Free Non-linear Integer Arithmetic (superset of QF_LIA)
    solver.set_option("produce-models", "true");

    let int_sort = tm.integer_sort();

    // Flatten the domain into one named-set per parameter.
    let domain_sets: Vec<NamedSet> = match &sig.domain {
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
            match parts.iter().map(|e| named_set(e)).collect::<Option<Vec<_>>>() {
                Some(sets) => sets,
                None => return CheckResult::Unknown("unsupported domain set expression".into()),
            }
        }
    };

    // Resolve range.
    let range_set = match named_set(&sig.range) {
        Some(s) => s,
        None => return CheckResult::Unknown("unsupported range set expression".into()),
    };

    // Declare one unconstrained integer variable per parameter.
    let param_terms: Vec<Term<'_>> = param_names
        .iter()
        .map(|n| tm.mk_const(int_sort.clone(), &n.0))
        .collect();

    // Build local variable environment: symbol → Term.
    let env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    // Assert domain membership for each parameter.
    for (term, set) in param_terms.iter().zip(domain_sets.iter()) {
        if let Some(constraint) = set_membership_constraint(&tm, term.clone(), set) {
            solver.assert_formula(constraint);
        }
        // `Int` has no constraint — nothing to assert.
    }

    // Encode the body as a cvc5 term, asserting call contracts along the way.
    let mut call_counter = 0usize;
    let body_term = match encode_expr(body, &env, fn_env, &tm, &mut solver, &mut call_counter) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    // Assert the negation of `body_term ∈ range`.
    match set_membership_constraint(&tm, body_term.clone(), &range_set) {
        None => {
            // Range is `Int` — any integer result qualifies, trivially proved.
            return CheckResult::Proved;
        }
        Some(range_holds) => {
            let negated = tm.mk_term(Kind::Not, &[range_holds]);
            solver.assert_formula(negated);
        }
    }

    // Ask the solver.
    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        let mut cex_params = HashMap::new();
        for (name, term) in param_names.iter().zip(param_terms.iter()) {
            let val = solver.get_value(term.clone());
            cex_params.insert(name.0.clone(), integer_value(&val));
        }
        let output_term = solver.get_value(body_term);
        CheckResult::Counterexample { params: cex_params, output: integer_value(&output_term) }
    } else {
        CheckResult::Unknown("solver returned unknown".into())
    }
}

// ── Named sets ────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
enum NamedSet {
    /// ℤ — all integers; no constraint.
    Int,
    /// { n ∈ ℤ | n ≥ 0 }
    Nat,
    /// { n ∈ ℤ | n > 0 }
    NatPos,
    /// { n ∈ ℤ | min ≤ n ≤ max }
    IntN { min: i64, max: i64 },
}

fn named_set(expr: &Expr) -> Option<NamedSet> {
    let ExprKind::Var(sym) = &expr.kind else { return None };
    Some(match sym.0.as_str() {
        "Int"    => NamedSet::Int,
        "Nat"    => NamedSet::Nat,
        "NatPos" => NamedSet::NatPos,
        "Int8"   => NamedSet::IntN { min: i8::MIN  as i64, max: i8::MAX  as i64 },
        "Int16"  => NamedSet::IntN { min: i16::MIN as i64, max: i16::MAX as i64 },
        "Int32"  => NamedSet::IntN { min: i32::MIN as i64, max: i32::MAX as i64 },
        "Int64"  => NamedSet::IntN { min: i64::MIN,        max: i64::MAX        },
        _ => return None,
    })
}

/// Build a cvc5 Term asserting `t ∈ set`, or `None` if no constraint (Int).
fn set_membership_constraint<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set: &NamedSet,
) -> Option<Term<'tm>> {
    match set {
        NamedSet::Int => None,
        NamedSet::Nat => {
            let zero = tm.mk_integer(0);
            Some(tm.mk_term(Kind::Geq, &[t, zero]))
        }
        NamedSet::NatPos => {
            let zero = tm.mk_integer(0);
            Some(tm.mk_term(Kind::Gt, &[t, zero]))
        }
        NamedSet::IntN { min, max } => {
            let lo  = tm.mk_integer(*min);
            let hi  = tm.mk_integer(*max);
            let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
            let leq = tm.mk_term(Kind::Leq, &[t, hi]);
            Some(tm.mk_term(Kind::And, &[geq, leq]))
        }
    }
}

// ── Expression encoding ───────────────────────────────────────────────────────

type Env<'tm> = HashMap<Symbol, Term<'tm>>;

/// Recursively encode a Cantor expression as a cvc5 `Term`.
///
/// When a function call is encountered, a fresh integer variable is introduced
/// for the return value, and the callee's per-signature contracts are asserted
/// as implications: `args ∈ domain → result ∈ range`.
fn encode_expr<'tm>(
    expr: &Expr,
    env: &Env<'tm>,
    fn_env: &FunctionEnv<'_>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
) -> Result<Term<'tm>, String> {
    match &expr.kind {
        ExprKind::IntLit(n) => Ok(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Ok(tm.mk_boolean(*b)),

        ExprKind::Var(sym) => env
            .get(sym)
            .cloned()
            .ok_or_else(|| format!("unbound variable `{}`", sym.0)),

        ExprKind::UnOp { op, expr: inner } => {
            let t = encode_expr(inner, env, fn_env, tm, solver, call_counter)?;
            match op {
                UnOp::Neg => Ok(tm.mk_term(Kind::Neg, &[t])),
                UnOp::Not => Ok(tm.mk_term(Kind::Not, &[t])),
            }
        }

        ExprKind::BinOp { op, lhs, rhs } => {
            let l = encode_expr(lhs, env, fn_env, tm, solver, call_counter)?;
            let r = encode_expr(rhs, env, fn_env, tm, solver, call_counter)?;
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
                BinOp::In | BinOp::NotIn
                | BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
                    return Err(format!("set operation `{op:?}` not yet encodable"))
                }
            };
            Ok(tm.mk_term(kind, &[l, r]))
        }

        ExprKind::If { cond, then_expr, else_expr } => {
            let c = encode_expr(cond, env, fn_env, tm, solver, call_counter)?;
            let t = encode_expr(then_expr, env, fn_env, tm, solver, call_counter)?;
            let e = encode_expr(else_expr, env, fn_env, tm, solver, call_counter)?;
            Ok(tm.mk_term(Kind::Ite, &[c, t, e]))
        }

        ExprKind::Call { callee, args } => {
            // Encode arguments.
            let arg_terms: Vec<Term<'_>> = args
                .iter()
                .map(|a| encode_expr(a, env, fn_env, tm, solver, call_counter))
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
    }
}

/// Assert `args ∈ domain → result ∈ range` for one callee signature.
///
/// If the domain or range is unsupported (non-integer named set), the
/// implication is silently skipped — the solver simply has less information,
/// which is safe (may produce Unknown rather than Proved, never a false Proved).
fn assert_call_contract<'tm>(
    sig: &FunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
) {
    // Resolve per-argument domain sets.
    let domain_sets: Vec<NamedSet> = match &sig.domain {
        None => vec![], // zero-arg callee
        Some(domain_expr) => {
            let parts = flatten_product(domain_expr);
            if parts.len() != arg_terms.len() {
                return; // arity mismatch — skip
            }
            match parts.iter().map(|e| named_set(e)).collect::<Option<Vec<_>>>() {
                Some(sets) => sets,
                None => return, // unsupported domain — skip
            }
        }
    };

    // Resolve range set.
    let range_set = match named_set(&sig.range) {
        Some(s) => s,
        None => return, // unsupported range — skip
    };

    // Build the antecedent: conjunction of per-arg domain constraints.
    // Constraints that are `None` (the arg is in `Int`) are dropped — they
    // contribute no information and would make the conjunction trivially false.
    let antecedents: Vec<Term<'_>> = domain_sets
        .iter()
        .zip(arg_terms.iter())
        .filter_map(|(set, term)| set_membership_constraint(tm, term.clone(), set))
        .collect();

    // Build the consequent: result ∈ range.
    let consequent = match set_membership_constraint(tm, result, &range_set) {
        Some(c) => c,
        None => return, // range is `Int` — trivially true, nothing to assert
    };

    // Combine into an implication (or bare consequent if domain is unconstrained).
    let formula = if antecedents.is_empty() {
        // No domain constraints → always applies → assert consequent directly.
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
