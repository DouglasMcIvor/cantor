//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionDef, FunctionSig, UnOp},
    span::{Span, Symbol},
};

use super::membership::{DistinctPreds, Membership, membership_constraint};
use super::NameDefs;

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
    pub(crate) violated_reason: String,
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
    name_defs: &NameDefs<'_>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    path_cond: Term<'tm>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, name_defs, fn_env, tm, solver, call_counter, builtin_obligs, path_cond.clone(), distinct_preds)
        };
    }

    match &expr.kind {
        ExprKind::IntLit(n) => Ok(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Ok(tm.mk_boolean(*b)),

        ExprKind::Var(sym) => {
            if let Some(term) = env.get(sym) {
                Ok(term.clone())
            } else if let Some(def) = name_defs.get(sym) {
                // Inline the definition's value expression (no params, same name_defs
                // so chained defs like `tau : Nat = 2 * pi` resolve correctly).
                encode_expr(&def.value, &Env::new(), name_defs, fn_env, tm, solver,
                            call_counter, builtin_obligs, path_cond, distinct_preds)
            } else {
                Err(format!("unbound variable `{}`", sym.0))
            }
        }

        ExprKind::UnOp { op, expr: inner } => {
            let t = enc!(inner)?;
            if let Some((domain, reason)) = unary_builtin_domain(op) {
                if let Membership::Constrained(c) = membership_constraint(tm, t.clone(), &domain, name_defs, distinct_preds) {
                    builtin_obligs.push(BuiltinObligation {
                        path_cond: path_cond.clone(),
                        obligation: c,
                        violated_reason: reason.to_string(),
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
                    // If the set RHS is a variable bound in the solver env it's a
                    // runtime set value — membership can't be decided at proof time.
                    if let ExprKind::Var(sym) = &rhs.kind {
                        if env.contains_key(sym) {
                            let fresh = format!("_in_{}", *call_counter);
                            *call_counter += 1;
                            return Ok(tm.mk_const(tm.boolean_sort(), &fresh));
                        }
                    }
                    let l = enc!(lhs)?;
                    return match membership_constraint(tm, l, rhs, name_defs, distinct_preds) {
                        Membership::Constrained(c)  => Ok(c),
                        Membership::Unconstrained    => Ok(tm.mk_boolean(true)),
                        Membership::Unsupported      => Err("unsupported set in `in` expression".into()),
                    };
                }
                BinOp::NotIn => {
                    if let ExprKind::Var(sym) = &rhs.kind {
                        if env.contains_key(sym) {
                            let fresh = format!("_in_{}", *call_counter);
                            *call_counter += 1;
                            let b = tm.mk_const(tm.boolean_sort(), &fresh);
                            return Ok(tm.mk_term(Kind::Not, &[b]));
                        }
                    }
                    let l = enc!(lhs)?;
                    return match membership_constraint(tm, l, rhs, name_defs, distinct_preds) {
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
                    if let Membership::Constrained(c) = membership_constraint(tm, (*arg_term).clone(), &domain, name_defs, distinct_preds) {
                        builtin_obligs.push(BuiltinObligation {
                            path_cond: path_cond.clone(),
                            obligation: c,
                            violated_reason: reason.to_string(),
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
                BinOp::Union | BinOp::ErrorUnion | BinOp::Intersect | BinOp::SymDiff => {
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
                then_expr, env, name_defs, fn_env, tm, solver, call_counter, builtin_obligs, then_guard, distinct_preds,
            )?;

            // Else-branch: path_cond ∧ ¬cond
            let not_c = tm.mk_term(Kind::Not, &[c.clone()]);
            let else_guard = tm.mk_term(Kind::And, &[path_cond, not_c]);
            let e = encode_expr(
                else_expr, env, name_defs, fn_env, tm, solver, call_counter, builtin_obligs, else_guard, distinct_preds,
            )?;

            Ok(tm.mk_term(Kind::Ite, &[c, t, e]))
        }

        ExprKind::Call { callee, args } => {
            // `size(s)` built-in: the exact cardinality is unknown at proof time;
            // model it as a fresh non-negative integer.
            if callee.0 == "size" && args.len() == 1 {
                let fresh = format!("_size_{}", *call_counter);
                *call_counter += 1;
                let result = tm.mk_const(tm.integer_sort(), &fresh);
                let non_neg = tm.mk_term(Kind::Geq, &[result.clone(), tm.mk_integer(0)]);
                solver.assert_formula(non_neg);
                return Ok(result);
            }

            // `from(x)` built-in: destructor for any `distinct` set.
            // For each distinct set D with basis B: is_D(arg) → result ∈ B.
            if callee.0 == "from" && args.len() == 1 {
                let arg_term = enc!(&args[0])?;
                let fresh = format!("_from_{}", *call_counter);
                *call_counter += 1;
                let result_var = tm.mk_const(tm.integer_sort(), &fresh);
                for (sym, pred) in distinct_preds {
                    if let Some(def) = name_defs.get(sym) {
                        let is_arg = tm.mk_term(Kind::ApplyUf, &[pred.clone(), arg_term.clone()]);
                        match membership_constraint(tm, result_var.clone(), &def.value, name_defs, distinct_preds) {
                            Membership::Unconstrained => {}
                            Membership::Constrained(basis_c) => {
                                solver.assert_formula(tm.mk_term(Kind::Implies, &[is_arg, basis_c]));
                            }
                            Membership::Unsupported => {}
                        }
                    }
                }
                return Ok(result_var);
            }

            // Auto-generated constructor: `litre(n)` for `Litre = distinct Nat`.
            // Detected by capitalising the first letter of callee and checking name_defs.
            if args.len() == 1 {
                if let Some(distinct_def) = distinct_def_for_constructor(callee, name_defs) {
                    if let Some(pred) = distinct_preds.get(&distinct_def.name) {
                        let arg_term = enc!(&args[0])?;
                        let fresh = format!("_call_{}", *call_counter);
                        *call_counter += 1;
                        let result_var = tm.mk_const(tm.integer_sort(), &fresh);
                        let is_result = tm.mk_term(Kind::ApplyUf, &[pred.clone(), result_var.clone()]);
                        match membership_constraint(tm, arg_term, &distinct_def.value, name_defs, distinct_preds) {
                            Membership::Unconstrained => solver.assert_formula(is_result),
                            Membership::Constrained(basis_c) => {
                                solver.assert_formula(tm.mk_term(Kind::Implies, &[basis_c, is_result]));
                            }
                            Membership::Unsupported => {}
                        }
                        return Ok(result_var);
                    }
                }
            }

            let arg_terms: Vec<Term<'_>> = args
                .iter()
                .map(|a| enc!(a))
                .collect::<Result<_, _>>()?;

            let callee_def = fn_env
                .get(callee)
                .ok_or_else(|| format!("unknown function `{}`", callee.0))?;

            let fresh = format!("_call_{}", *call_counter);
            *call_counter += 1;

            // For tuple-returning callees, decompose the result into leaf scalar
            // constants assembled with mk_tuple — same reason as for tuple params:
            // a symbolic tuple constant can't be used with child() extraction.
            let result_var = if let Some(first_sig) = callee_def.sigs.first() {
                if is_product_range(&first_sig.range) {
                    let (assembled, leaves) = mk_decomposed_tuple(tm, &fresh, &first_sig.range);
                    for (leaf, leaf_set) in leaves {
                        match membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds) {
                            Membership::Constrained(c) => solver.assert_formula(c),
                            _ => {}
                        }
                    }
                    assembled
                } else {
                    let sort = set_sort_for_range(tm, &first_sig.range);
                    tm.mk_const(sort, &fresh)
                }
            } else {
                tm.mk_const(tm.integer_sort(), &fresh)
            };

            for sig in &callee_def.sigs {
                assert_call_contract(sig, &arg_terms, result_var.clone(), tm, solver, name_defs, distinct_preds);
            }

            Ok(result_var)
        }

        ExprKind::SetLit(_) | ExprKind::Comprehension { .. } => {
            Err("set expressions cannot appear in value position (only in domain/range/`in`/`for` positions)".into())
        }

        // For `A !! B` callees, assert that the result is in the success type A.
        // This is sound because `?` only continues on the success path — failures
        // propagate immediately — so any value that reaches the next statement
        // must satisfy A.  Without this assertion the solver cannot prove bindings
        // like `result : Nat = fetch(x)?` because the callee contract allows error
        // payloads (very negative sentinels) as well as success values.
        ExprKind::Try(inner) => {
            let result = enc!(inner)?;
            if let ExprKind::Call { callee, .. } = &inner.kind {
                if let Some(callee_def) = fn_env.get(callee) {
                    if let Some(sig) = callee_def.sigs.first() {
                        if let ExprKind::BinOp {
                            op: BinOp::ErrorUnion,
                            lhs: success_type,
                            ..
                        } = &sig.range.kind
                        {
                            if let Membership::Constrained(c) =
                                membership_constraint(tm, result.clone(), success_type, name_defs, distinct_preds)
                            {
                                solver.assert_formula(c);
                            }
                        }
                    }
                }
            }
            Ok(result)
        }

        // `fail` — encode as the FAIL_SENTINEL constant (i64::MIN).
        ExprKind::FailLit => Ok(tm.mk_integer(i64::MIN)),

        // `fail expr` — encodes as a very negative integer (FAIL_SENTINEL + expr + 1).
        // The solver sees this as a concrete value; contracts on `!!` ranges use
        // Unconstrained so the solver never needs to reason about this encoding.
        ExprKind::FailWith(inner) => {
            let n = enc!(inner)?;
            let base = tm.mk_integer(i64::MIN.wrapping_add(1));
            Ok(tm.mk_term(Kind::Add, &[base, n]))
        }

        // `(e0, e1, …)` — build a cvc5 tuple term.
        ExprKind::Tuple(elems) => {
            let terms: Vec<Term<'_>> = elems.iter()
                .map(|e| enc!(e))
                .collect::<Result<_, _>>()?;
            Ok(tm.mk_tuple(&terms))
        }

        // `base.N` — project element N from a cvc5 tuple.
        //
        // We use `child(index + 1)` rather than `TupleProject` because
        // APPLY_CONSTRUCTOR has the constructor as child(0) and elements at
        // child(1+i).  TupleProject produces a datatype-theory term that
        // cvc5 rejects in arithmetic contexts (Geq, Add, …) even though its
        // sort is integer.  child(1+i) extracts the actual scalar child term
        // directly, which IS recognised as arithmetic.
        ExprKind::Proj { base, index } => {
            let base_term = enc!(base)?;
            Ok(base_term.child(*index + 1))
        }
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
    name_defs: &NameDefs<'_>,
    distinct_preds: &DistinctPreds<'tm>,
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
                match membership_constraint(tm, arg.clone(), part, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => antecedents.push(c),
                    Membership::Unsupported => return,
                }
            }
        }
    }

    let consequent = match membership_constraint(tm, result, &sig.range, name_defs, distinct_preds) {
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

/// Create a decomposed representation of a tuple-typed term.
///
/// For a product set `A * B`, creates individual leaf scalar constants
/// and assembles them with `mk_tuple`. This avoids symbolic tuple-sorted
/// constants, which cvc5 rejects when used in arithmetic contexts via
/// `TupleProject` (beta-reduction only works on `mk_tuple(...)` terms).
///
/// Returns `(assembled_term, leaves)` where each leaf is `(leaf_term, leaf_set_expr)`.
/// The caller asserts membership for each leaf separately (scalars are arithmetic-safe).
pub(crate) fn mk_decomposed_tuple<'tm, 'e>(
    tm: &'tm TermManager,
    name: &str,
    set_expr: &'e Expr,
) -> (Term<'tm>, Vec<(Term<'tm>, &'e Expr)>) {
    let parts = flatten_product(set_expr);
    if parts.len() <= 1 {
        let sort = set_sort(tm, set_expr);
        let leaf = tm.mk_const(sort, name);
        return (leaf.clone(), vec![(leaf, set_expr)]);
    }
    let mut leaves = Vec::new();
    let mut child_terms = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        let child_name = format!("{name}__{i}");
        let (child_term, child_leaves) = mk_decomposed_tuple(tm, &child_name, part);
        leaves.extend(child_leaves);
        child_terms.push(child_term);
    }
    (tm.mk_tuple(&child_terms), leaves)
}

/// SMT sort for a set expression: Bool → boolean, `A * B` → tuple sort, else integer.
pub(crate) fn set_sort<'tm>(tm: &'tm TermManager, set_expr: &Expr) -> Sort<'tm> {
    match &set_expr.kind {
        ExprKind::Var(sym) if sym.0 == "Bool" => tm.boolean_sort(),
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            let parts = flatten_product(set_expr);
            let sorts: Vec<Sort<'_>> = parts.iter().map(|p| set_sort(tm, p)).collect();
            tm.mk_tuple_sort(&sorts)
        }
        _ => tm.integer_sort(),
    }
}

/// SMT sort for a range expression (strips `Fail`, `Union`, `ErrorUnion` wrappers).
pub(crate) fn set_sort_for_range<'tm>(tm: &'tm TermManager, range: &Expr) -> Sort<'tm> {
    match &range.kind {
        ExprKind::Var(sym) if sym.0 == "Fail" => tm.integer_sort(),
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, .. } => set_sort_for_range(tm, lhs),
        ExprKind::BinOp { op: BinOp::ErrorUnion, lhs, .. } => set_sort_for_range(tm, lhs),
        _ => set_sort(tm, range),
    }
}

/// True if the range (after stripping Fail/Union/ErrorUnion wrappers) is a product type.
fn is_product_range(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::BinOp { op: BinOp::Mul, .. } => true,
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, .. } => is_product_range(lhs),
        ExprKind::BinOp { op: BinOp::ErrorUnion, lhs, .. } => is_product_range(lhs),
        ExprKind::Var(sym) if sym.0 == "Fail" => false,
        _ => false,
    }
}

/// If `callee` is the auto-generated constructor for a `distinct` set
/// (i.e. its name with the first letter uppercased is a `Distinct` NameDef),
/// return that NameDef.
pub(crate) fn distinct_def_for_constructor<'a>(
    callee: &Symbol,
    name_defs: &'a NameDefs<'_>,
) -> Option<&'a crate::ast::NameDef> {
    use crate::ast::DefKind;
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    let sym = Symbol::new(capitalized);
    name_defs.get(&sym).filter(|def| def.kind == DefKind::Distinct).copied()
}
