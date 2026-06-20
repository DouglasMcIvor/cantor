//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionDef, FunctionSig, UnOp},
    span::{Span, Symbol},
};

use super::membership::{Membership, membership_constraint};

// ── Environment ───────────────────────────────────────────────────────────────

/// Map from variable name to its current SSA cvc5 term.
pub(crate) type Env<'tm> = HashMap<Symbol, Term<'tm>>;

// ── Built-in operator domain table ───────────────────────────────────────────

/// A proof obligation produced when encoding a built-in operator argument.
///
/// The caller asserts `path_cond → obligation` and, on a SAT result,
/// inspects the model to report `violated_reason` in the counterexample.
pub(crate) struct BuiltinObligation<'tm> {
    pub(crate) path_cond: Term<'tm>,
    pub(crate) obligation: Term<'tm>,
    pub(crate) violated_reason: &'static str,
}

/// Domain constraint for argument `arg_idx` (0-based) of a binary built-in.
///
/// `None` means the argument is unconstrained (accepts any `Int`).
/// This is the authoritative table of every binary operator's argument types.
pub(crate) fn binary_builtin_domain(op: &BinOp, arg_idx: usize) -> Option<(Expr, &'static str)> {
    match (op, arg_idx) {
        (BinOp::Div, 1) => Some((named_set("NonZeroInt"), "division by zero")),
        _ => None,
    }
}

/// Domain constraint for the operand of a unary built-in.
///
/// `None` means unconstrained.
pub(crate) fn unary_builtin_domain(op: &UnOp) -> Option<(Expr, &'static str)> {
    match op {
        UnOp::Neg => None, // Int -> Int
        UnOp::Not => None, // Bool -> Bool (Bool not yet a solver-visible type)
    }
}

/// Build a `Var` expression that refers to a named built-in set.
pub(crate) fn named_set(name: &'static str) -> Expr {
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
/// built-in operator argument that has a domain constraint; the caller then
/// asserts `path_cond → obligation` for each, giving path-sensitive checking.
pub(crate) fn encode_expr<'tm>(
    expr: &Expr,
    env: &Env<'tm>,
    const_defs: &HashMap<Symbol, &Expr>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    path_cond: Term<'tm>,
) -> Result<Term<'tm>, String> {
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

            let callee_def = fn_env
                .get(callee)
                .ok_or_else(|| format!("unknown function `{}`", callee.0))?;

            let fresh = format!("_call_{}", *call_counter);
            *call_counter += 1;
            let result_var = tm.mk_const(tm.integer_sort(), &fresh);

            for sig in &callee_def.sigs {
                assert_call_contract(sig, &arg_terms, result_var.clone(), tm, solver);
            }

            Ok(result_var)
        }

        ExprKind::SetLit(_) | ExprKind::Comprehension { .. } => {
            Err("set expressions cannot appear in value position (only in domain/range/`in`/`for` positions)".into())
        }

        // At the SMT level `?` is transparent: we reason only about the success
        // path, so the callee's contract (domain → range) already constrains the
        // result variable.  Runtime failure propagation is a codegen concern.
        ExprKind::Try(inner) => enc!(inner),
    }
}

// ── Call contract assertion ───────────────────────────────────────────────────

/// Assert `args ∈ domain → result ∈ range` for one callee signature.
///
/// If any part of the domain or range is unsupported, the implication is
/// silently skipped — the solver has less information but never incorrect info.
pub(crate) fn assert_call_contract<'tm>(
    sig: &FunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
) {
    let mut antecedents: Vec<Term<'_>> = Vec::new();
    match &sig.domain {
        None => {}
        Some(domain_expr) => {
            let parts = flatten_product(domain_expr);
            if parts.len() != arg_terms.len() {
                return;
            }
            for (part, arg) in parts.iter().zip(arg_terms.iter()) {
                match membership_constraint(tm, arg.clone(), part) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => antecedents.push(c),
                    Membership::Unsupported => return,
                }
            }
        }
    }

    let consequent = match membership_constraint(tm, result, &sig.range) {
        Membership::Unconstrained => return,
        Membership::Constrained(c) => c,
        Membership::Unsupported => return,
    };

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
pub(crate) fn flatten_product(expr: &Expr) -> Vec<&Expr> {
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
pub(crate) fn integer_value(term: &Term<'_>) -> i64 {
    if term.is_int32_value() {
        term.int32_value() as i64
    } else if term.is_int64_value() {
        term.int64_value()
    } else {
        term.to_string().trim().parse::<i64>().unwrap_or(0)
    }
}

/// Extract a bool from a cvc5 boolean model term.
pub(crate) fn boolean_value(term: &Term<'_>) -> bool {
    term.to_string().trim() == "true"
}
