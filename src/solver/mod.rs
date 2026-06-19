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

    // Encode the body as a cvc5 term, asserting call contracts along the way.
    let mut call_counter = 0usize;
    let body_term = match encode_expr(body, &env, fn_env, &tm, &mut solver, &mut call_counter) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    // Assert the negation of `body_term ∈ range`.
    match membership_constraint(&tm, body_term.clone(), &sig.range) {
        Membership::Unconstrained => {
            // Range is `Int` — any integer output qualifies; trivially proved.
            return CheckResult::Proved;
        }
        Membership::Constrained(range_holds) => {
            let negated = tm.mk_term(Kind::Not, &[range_holds]);
            solver.assert_formula(negated);
        }
        Membership::Unsupported => {
            return CheckResult::Unknown("unsupported range set expression".into())
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
            "Int"    => Membership::Unconstrained,
            "Nat"    => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Geq, &[t, zero]))
            }
            "NatPos" => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Gt, &[t, zero]))
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

        ExprKind::SetLit(_) => {
            Err("set literals cannot appear in function bodies".into())
        }
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
