//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{DatatypeConstructorDecl, Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionDef, FunctionSig, UnOp},
    kind::{Kind as ValKind, leaf_count, set_kind as val_set_kind},
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

/// Domain constraints for argument `arg_idx` (0-based) of a binary built-in.
///
/// Returns a list of `(set, reason)` pairs; each pair generates a proof obligation
/// that the argument belongs to `set`.  An empty list means unconstrained.
/// Multiple constraints are checked independently (e.g. the `/` divisor needs
/// both `Int` and `NonZeroInt`).
///
/// `In`/`NotIn` are handled by early-return paths before this is called —
/// passing either here is a programming error and will panic.
pub(crate) fn binary_builtin_domain(op: &BinOp, arg_idx: usize) -> Vec<(Expr, &'static str)> {
    match (op, arg_idx) {
        // ── Arithmetic ────────────────────────────────────────────────────────
        // Div arg 1: divisor must be a plain Int AND non-zero.
        (BinOp::Div, 1) => vec![
            (named_set("Int"),        "divisor must be Int, not a member of a distinct set"),
            (named_set("NonZeroInt"), "division by zero"),
        ],
        // All arithmetic args must be plain Int (not Bool, not a distinct set).
        (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div, _) => vec![
            (named_set("Int"), "operand must be Int, not a member of a distinct set"),
        ],
        // ── Comparisons ───────────────────────────────────────────────────────
        (BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge, _) => vec![],
        // ── Logical ───────────────────────────────────────────────────────────
        // Both args of `and`/`or` must be in Bool.
        (BinOp::And | BinOp::Or, _) => vec![(named_set("Bool"), "operand of logical operator must be Bool")],
        // ── Set operations ────────────────────────────────────────────────────
        (BinOp::Union | BinOp::Intersect | BinOp::SymDiff, _) => vec![],
        // ── Must never reach here ─────────────────────────────────────────────
        (BinOp::In | BinOp::NotIn, _) => {
            panic!("binary_builtin_domain called with In/NotIn — handled before the domain-check loop")
        }
    }
}

/// Domain constraints for the operand of a unary built-in.
///
/// Returns a list of `(set, reason)` pairs; empty means unconstrained.
pub(crate) fn unary_builtin_domain(op: &UnOp) -> Vec<(Expr, &'static str)> {
    match op {
        // Negation is defined on Int only — distinct sets cannot be negated.
        UnOp::Neg => vec![(named_set("Int"), "operand of negation must be Int, not a member of a distinct set")],
        // Operand of `not` must be in Bool.
        UnOp::Not => vec![(named_set("Bool"), "operand of `not` must be Bool")],
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
    // When `Some(sort)`, coerce integer/boolean/tuple-sorted results to that
    // datatype sort.  Used to unify cross-kind union if/else branches so both
    // arms have the same CVC5 sort before `Ite` is applied.
    // Early-returning paths (membership predicates, built-in calls) bypass
    // this coercion intentionally — they produce predicates, not union values.
    coerce_to: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, name_defs, fn_env, tm, solver, call_counter, builtin_obligs, path_cond.clone(), distinct_preds, None)
        };
    }

    let term = match &expr.kind {
        ExprKind::IntLit(n) => Ok(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Ok(tm.mk_boolean(*b)),

        ExprKind::Var(sym) => {
            if let Some(term) = env.get(sym) {
                Ok(term.clone())
            } else if let Some(def) = name_defs.get(sym) {
                // Inline the definition's value expression (no params, same name_defs
                // so chained defs like `tau : Nat = 2 * pi` resolve correctly).
                encode_expr(&def.value, &Env::new(), name_defs, fn_env, tm, solver,
                            call_counter, builtin_obligs, path_cond, distinct_preds, None)
            } else {
                Err(format!("unbound variable `{}`", sym.0))
            }
        }

        ExprKind::UnOp { op, expr: inner } => {
            let t = enc!(inner)?;
            for (domain, reason) in unary_builtin_domain(op) {
                if let Membership::Constrained(c) = membership_constraint(tm, t.clone(), &domain, name_defs, distinct_preds) {
                    builtin_obligs.push(BuiltinObligation {
                        path_cond: path_cond.clone(),
                        obligation: c,
                        violated_reason: reason.to_string(),
                    });
                }
            }
            match op {
                UnOp::Neg => {
                    // Guard: wrong-sort operand (e.g. distinct-sort) — domain check
                    // pushed Constrained(false); return dummy to avoid CVC5 sort panic.
                    if !t.sort().is_integer() { return Ok(tm.mk_integer(0)); }
                    Ok(tm.mk_term(Kind::Neg, &[t]))
                }
                UnOp::Not => {
                    // Guard: wrong-sort operand — domain check pushed Constrained(false);
                    // return dummy to avoid CVC5 sort panic.
                    if !t.sort().is_boolean() { return Ok(tm.mk_boolean(false)); }
                    Ok(tm.mk_term(Kind::Not, &[t]))
                }
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
                for (domain, reason) in binary_builtin_domain(op, arg_idx) {
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
                BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
                    return Err(format!("set operation `{op:?}` not yet encodable"))
                }
            };
            // Guard: bail out with a sort-safe dummy when operands have the wrong sort.
            // The domain checks above push Constrained(false) obligations that cause
            // a counterexample; the dummy prevents a CVC5 sort panic.
            if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div
                              | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                && (!l.sort().is_integer() || !r.sort().is_integer())
            {
                return Ok(tm.mk_integer(0));
            }
            if matches!(op, BinOp::And | BinOp::Or)
                && (!l.sort().is_boolean() || !r.sort().is_boolean())
            {
                return Ok(tm.mk_boolean(false));
            }
            Ok(tm.mk_term(kind, &[l, r]))
        }

        ExprKind::If { cond, then_expr, else_expr } => {
            let c = enc!(cond)?;

            // CVC5 requires a boolean-sort condition for Ite.  If the encoded
            // condition is integer-sort (e.g. a variable from a Bool|Nat domain),
            // coerce it to boolean via `c != 0` (0 = false, non-zero = true).
            let c_bool = if c.sort().is_boolean() {
                c
            } else {
                tm.mk_term(Kind::Distinct, &[c, tm.mk_integer(0)])
            };

            // Then-branch: path_cond ∧ cond — propagate coerce_to so the branch
            // result is wrapped in the union datatype if needed.
            let then_guard = tm.mk_term(Kind::And, &[path_cond.clone(), c_bool.clone()]);
            let t = encode_expr(
                then_expr, env, name_defs, fn_env, tm, solver, call_counter, builtin_obligs, then_guard, distinct_preds, coerce_to.clone(),
            )?;

            // Else-branch: path_cond ∧ ¬cond
            let not_c = tm.mk_term(Kind::Not, &[c_bool.clone()]);
            let else_guard = tm.mk_term(Kind::And, &[path_cond.clone(), not_c]);
            let e = encode_expr(
                else_expr, env, name_defs, fn_env, tm, solver, call_counter, builtin_obligs, else_guard, distinct_preds, coerce_to.clone(),
            )?;

            // CVC5 requires both branches to have the same sort.
            // Unify sorts before calling mk_term(Ite, …).
            let (t, e) = if t.sort() == e.sort() {
                (t, e)
            } else if (t.sort().is_boolean() && e.sort().is_integer())
                || (t.sort().is_integer() && e.sort().is_boolean())
            {
                // Bool ↔ Int unification: false = 0, true = 1 in Cantor's value model.
                // One branch is boolean-sort (a literal or Bool param), the other is
                // integer-sort.  Coerce the boolean to 0/1 so Ite gets matching sorts.
                let bool_to_int = |b: Term<'tm>| {
                    if b.sort().is_boolean() {
                        tm.mk_term(Kind::Ite, &[b, tm.mk_integer(1), tm.mk_integer(0)])
                    } else {
                        b
                    }
                };
                (bool_to_int(t), bool_to_int(e))
            } else {
                // One or both branches have a sort that doesn't match the target and
                // can't be trivially unified.  For each such branch:
                // - integer-sort → pass through
                // - boolean-sort → coerce to 0/1
                // - anything else (distinct sort, tuple, future Float32, …) → the value
                //   can never satisfy an integer-sort range; push a path-conditioned
                //   `false` obligation so the solver finds a counterexample when execution
                //   steers into that branch, and use a dummy integer so the Ite stays
                //   well-sorted.
                let mut to_int_or_dummy = |b: Term<'tm>, path: Term<'tm>| {
                    if b.sort().is_integer() {
                        b
                    } else if b.sort().is_boolean() {
                        tm.mk_term(Kind::Ite, &[b, tm.mk_integer(1), tm.mk_integer(0)])
                    } else {
                        builtin_obligs.push(BuiltinObligation {
                            path_cond: path,
                            obligation: tm.mk_boolean(false),
                            violated_reason: "branch value's set cannot satisfy the range"
                                .to_string(),
                        });
                        tm.mk_integer(0)
                    }
                };
                let not_c = tm.mk_term(Kind::Not, &[c_bool.clone()]);
                let then_path = tm.mk_term(Kind::And, &[path_cond.clone(), c_bool.clone()]);
                let else_path = tm.mk_term(Kind::And, &[path_cond.clone(), not_c]);
                (to_int_or_dummy(t, then_path), to_int_or_dummy(e, else_path))
            };

            Ok(tm.mk_term(Kind::Ite, &[c_bool, t, e]))
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
            // Identify the distinct set by sort-matching, apply the `from` UF,
            // and assert the basis membership constraint on the result on-demand.
            if callee.0 == "from" && args.len() == 1 {
                let arg_term = enc!(&args[0])?;
                for (sym, info) in distinct_preds {
                    if arg_term.sort() == info.sort {
                        let result = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), arg_term]);
                        if let Some(def) = name_defs.get(sym) {
                            match membership_constraint(tm, result.clone(), &def.value, name_defs, distinct_preds) {
                                Membership::Constrained(c) => solver.assert_formula(c),
                                _ => {}
                            }
                        }
                        return Ok(result);
                    }
                }
                return Err("from() applied to a value that is not a member of any distinct set".into());
            }

            // Auto-generated constructor: `litre(n)` for `Litre = distinct Nat`.
            // Detected by capitalising the first letter of callee and checking name_defs.
            // Apply the `mk` UF — result has sort D_sort (distinct sort).
            // Emit a basis obligation so `litre(x)` with x : Int is rejected when x ∉ Nat.
            if args.len() == 1 {
                if let Some(distinct_def) = distinct_def_for_constructor(callee, name_defs) {
                    if let Some(info) = distinct_preds.get(&distinct_def.name) {
                        let arg_term = enc!(&args[0])?;
                        match membership_constraint(tm, arg_term.clone(), &distinct_def.value, name_defs, distinct_preds) {
                            Membership::Constrained(c) => builtin_obligs.push(BuiltinObligation {
                                path_cond: path_cond.clone(),
                                obligation: c,
                                violated_reason: format!(
                                    "argument to {}() must satisfy the basis constraint",
                                    callee.0
                                ),
                            }),
                            Membership::Unconstrained => {}
                            Membership::Unsupported => {}
                        }
                        let result = tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), arg_term]);
                        return maybe_coerce(tm, result, &coerce_to, distinct_preds);
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
                    let (assembled, leaves) = mk_decomposed_tuple(tm, &fresh, &first_sig.range, distinct_preds);
                    for (leaf, leaf_set) in leaves {
                        match membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds) {
                            Membership::Constrained(c) => solver.assert_formula(c),
                            _ => {}
                        }
                    }
                    assembled
                } else {
                    match set_sort_for_range(tm, &first_sig.range, distinct_preds) {
                        Some(sort) => tm.mk_const(sort, &fresh),
                        None => return Err(format!(
                            "call to `{}` has an unsupported range sort (internal error)",
                            callee.0
                        )),
                    }
                }
            } else {
                tm.mk_const(tm.integer_sort(), &fresh)
            };

            for sig in &callee_def.sigs {
                assert_call_contract(sig, &arg_terms, result_var.clone(), tm, solver, name_defs, distinct_preds);
            }

            Ok(result_var)
        }

        ExprKind::SetLit(_) | ExprKind::Comprehension { .. } | ExprKind::KleeneStar(_) => {
            Err("set expressions cannot appear in value position (only in domain/range/`in`/`for` positions)".into())
        }

        // For `A !! B` callees, assert that the result is in the success type A.
        // This is sound because `?` only continues on the success path — failures
        // propagate immediately — so any value that reaches the next statement
        // must satisfy A.  Without this assertion the solver cannot prove bindings
        // like `result : Nat = fetch(x)?` because the callee contract allows error
        // payloads (very negative sentinels) as well as success values.
        // After `?` propagation succeeds, the result must be in the success set.
        // We assert this so the solver knows the failure arm has been stripped.
        // This is needed for both `| Fail` and `!! Y` (= `| (Fail * Y)`) callees.
        ExprKind::Try(inner) => {
            let result = enc!(inner)?;
            if let ExprKind::Call { callee, .. } = &inner.kind {
                if let Some(callee_def) = fn_env.get(callee) {
                    if let Some(sig) = callee_def.sigs.first() {
                        if let Some(success_type) = success_arm_of_range(&sig.range) {
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
        //
        // Projection on a cross-kind union (datatype-sorted) value is not
        // supported without first discriminating the arm; return Unknown.
        ExprKind::Proj { base, index } => {
            let base_term = enc!(base)?;
            // CVC5 tuple sorts also satisfy is_dt() == true; we only want to reject
            // non-tuple algebraic datatypes (i.e., cross-kind union values from Step 6).
            if base_term.sort().is_dt() && !base_term.sort().is_tuple() {
                return Err(
                    "projection on a cross-kind union value is not yet supported \
                     in the solver — discriminate the arm with `in` first"
                        .to_string(),
                );
            }
            Ok(base_term.child(*index + 1))
        }
    }?;

    // Apply coercion for cross-kind union contexts (e.g. if/else branches).
    // Constructor early-returns in ExprKind::Call also call maybe_coerce directly.
    maybe_coerce(tm, term, &coerce_to, distinct_preds)
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
    distinct_preds: &DistinctPreds<'tm>,
) -> (Term<'tm>, Vec<(Term<'tm>, &'e Expr)>) {
    let parts = flatten_product(set_expr);
    if parts.len() <= 1 {
        // Only called for product set expressions whose leaves always have a defined sort.
        let sort = set_sort(tm, set_expr, distinct_preds)
            .expect("mk_decomposed_tuple: leaf set expression has no representable CVC5 sort");
        let leaf = tm.mk_const(sort, name);
        return (leaf.clone(), vec![(leaf, set_expr)]);
    }
    let mut leaves = Vec::new();
    let mut child_terms = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        let child_name = format!("{name}__{i}");
        let (child_term, child_leaves) = mk_decomposed_tuple(tm, &child_name, part, distinct_preds);
        leaves.extend(child_leaves);
        child_terms.push(child_term);
    }
    (tm.mk_tuple(&child_terms), leaves)
}

// ── Cross-kind union datatype helpers ─────────────────────────────────────────

/// Flatten a left-associative `A | B | C` or `A + B + C` into `[A, B, C]`.
///
/// Used when building a CVC5 algebraic datatype for a cross-kind union so that
/// `(A | B) | C` gives `[A, B, C]` rather than `[[A, B], C]`.
pub(crate) fn flatten_any_union(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let mut arms = flatten_any_union(lhs);
            arms.push(rhs);
            arms
        }
        _ => vec![expr],
    }
}

/// Canonical CVC5 constructor name for a cross-kind union arm, derived from its `Kind`.
///
/// Used both when creating the datatype sort in `set_sort` and when looking up
/// the right constructor in `membership_constraint`, so the names must match
/// exactly.
pub(crate) fn arm_ctor_name(k: &ValKind) -> String {
    match k {
        ValKind::Int           => "ck_Int".to_string(),
        ValKind::Bool          => "ck_Bool".to_string(),
        ValKind::Fail          => "ck_Fail".to_string(),
        ValKind::Set(_)        => "ck_Set".to_string(),
        ValKind::Union(_)      => "ck_Union".to_string(),
        ValKind::Tuple(inner)  => {
            let s = inner.iter().map(arm_ctor_name).collect::<Vec<_>>().join("_");
            format!("ck_T_{s}")
        }
        ValKind::TaggedUnion(arms) => {
            let s = arms.iter().map(arm_ctor_name).collect::<Vec<_>>().join("_");
            format!("ck_TU_{s}")
        }
        // TODO: Kleene-star Vector kind cannot be an arm of a cross-kind union yet.
        ValKind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in arm_ctor_name"),
    }
}

/// Constructor name for a union arm, with distinct-set awareness.
///
/// Distinct-set arms get `"ck_D_{Name}"` so they never collide with `"ck_Int"` from
/// scalar arms — even though both would produce `ValKind::Int` via `val_set_kind`.
/// All other arms delegate to `arm_ctor_name`.
///
/// This must be used wherever `arm_ctor_name` was previously used for individual arms
/// in the union-datatype pipeline (creation in `build_union_datatype_sort` and lookup
/// in `membership_constraint_for_dt`) so the names always match.
pub(crate) fn arm_ctor_name_for_arm<'tm>(
    arm_expr: &Expr,
    distinct_preds: &DistinctPreds<'tm>,
) -> String {
    if let ExprKind::Var(sym) = &arm_expr.kind {
        if distinct_preds.contains_key(sym) {
            return format!("ck_D_{}", sym.0);
        }
    }
    arm_ctor_name(&val_set_kind(arm_expr))
}

/// Build a CVC5 algebraic datatype sort for a cross-kind union.
///
/// Each arm gets one constructor:
/// - Distinct-set arms: named `"ck_D_{Name}"` with one selector of the set's
///   uninterpreted sort.
/// - All other arms: named via `arm_ctor_name` with one `integer_sort` selector
///   per i64 leaf of the arm's `Kind`.
///
/// Arms are listed in the order determined by `flatten_any_union`.
fn build_union_datatype_sort<'tm>(
    tm: &'tm TermManager,
    arms: &[&Expr],
    distinct_preds: &DistinctPreds<'tm>,
) -> Sort<'tm> {
    let int_sort = tm.integer_sort();
    // Collect (ctor_name, field_sorts) per arm.
    let arm_infos: Vec<(String, Vec<Sort<'_>>)> = arms.iter().map(|arm_expr| {
        if let ExprKind::Var(sym) = &arm_expr.kind {
            if let Some(info) = distinct_preds.get(sym) {
                return (format!("ck_D_{}", sym.0), vec![info.sort.clone()]);
            }
        }
        let kind = val_set_kind(arm_expr);
        let ctor_name = arm_ctor_name(&kind);
        let fields = (0..leaf_count(&kind)).map(|_| int_sort.clone()).collect();
        (ctor_name, fields)
    }).collect();

    let dt_name = format!(
        "CKU_{}",
        arm_infos.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join("_")
    );
    let mut dt_decl = tm.mk_dt_decl(&dt_name, false);
    for (ctor_name, field_sorts) in &arm_infos {
        let mut ctor: DatatypeConstructorDecl<'_> = tm.mk_dt_cons_decl(ctor_name);
        for (j, sort) in field_sorts.iter().enumerate() {
            ctor.add_selector(&format!("f{j}"), sort.clone());
        }
        dt_decl.add_constructor(&ctor);
    }
    tm.mk_dt_sort(&dt_decl)
}

// ── Coerce-to-union helpers ───────────────────────────────────────────────────

/// Map a CVC5 sort back to the `ValKind` we used to create it, so we can
/// derive the canonical constructor name for coercion.
///
/// Only handles the sorts produced by `set_sort`: integer, boolean, and
/// tuple sorts over integer/boolean leaves.
fn cvc5_sort_to_valkind(sort: &Sort<'_>) -> ValKind {
    if sort.is_boolean() {
        ValKind::Bool
    } else if sort.is_integer() {
        ValKind::Int
    } else if sort.is_tuple() {
        let dt = sort.datatype();
        let ctor = dt.constructor(0); // tuple has exactly one constructor
        let inner: Vec<ValKind> = (0..ctor.num_selectors())
            .map(|j| cvc5_sort_to_valkind(&ctor.selector(j).codomain_sort()))
            .collect();
        ValKind::Tuple(inner)
    } else {
        panic!("cvc5_sort_to_valkind: unhandled sort; this is a bug")
    }
}

/// Flatten a CVC5 term into integer-sorted leaf terms matching the tagged-union
/// datatype field layout (all selectors are `integer_sort`).
///
/// Boolean-sorted terms are converted to 0/1 integers.
/// Tuple-sorted terms are flattened depth-first using `child(i+1)`.
fn leaves_from_cvc5_term<'tm>(
    tm: &'tm TermManager,
    val: Term<'tm>,
    kind: &ValKind,
) -> Vec<Term<'tm>> {
    match kind {
        ValKind::Bool => {
            let one  = tm.mk_integer(1);
            let zero = tm.mk_integer(0);
            vec![tm.mk_term(Kind::Ite, &[val, one, zero])]
        }
        ValKind::Int => vec![val],
        ValKind::Tuple(inner) => inner
            .iter()
            .enumerate()
            .flat_map(|(i, k)| leaves_from_cvc5_term(tm, val.child(i + 1), k))
            .collect(),
        _ => panic!("leaves_from_cvc5_term: unhandled kind {:?}; this is a bug", kind),
    }
}

/// Wrap `val` (integer-, boolean-, or tuple-sorted) into the matching constructor
/// of `dt_sort` (a cross-kind union algebraic datatype built by `build_union_datatype_sort`).
///
/// Returns `Err` if `dt_sort` has no constructor matching `val`'s sort — which
/// means the value's sort is not an arm of the target union (a type error in the
/// source program that the solver should report as Unknown).
fn coerce_to_union_dt<'tm>(
    tm: &'tm TermManager,
    val: Term<'tm>,
    dt_sort: &Sort<'tm>,
) -> Result<Term<'tm>, String> {
    let val_kind  = cvc5_sort_to_valkind(&val.sort());
    let ctor_name = arm_ctor_name(&val_kind);
    let dt = dt_sort.datatype();
    let ctor = (0..dt.num_constructors())
        .map(|i| dt.constructor(i))
        .find(|c| c.name() == ctor_name)
        .ok_or_else(|| format!(
            "coerce_to_union_dt: no constructor '{ctor_name}' in target datatype; \
             the expression's sort is not an arm of the declared union"
        ))?;

    let fields = leaves_from_cvc5_term(tm, val, &val_kind);
    let mut args: Vec<Term<'_>> = vec![ctor.term()];
    args.extend(fields);
    Ok(tm.mk_term(Kind::ApplyConstructor, &args))
}

/// Coerce `term` to `coerce_to` sort if the target is a cross-kind union DT.
///
/// Handles three cases:
/// - Integer/Boolean/Tuple-sorted terms → existing `coerce_to_union_dt` path.
/// - Distinct-sorted terms → wrapped in the `"ck_D_{Name}"` constructor.
/// - Same sort or no coerce target → returned unchanged.
///
/// Used both at the end of `encode_expr` (general case) and at early-return
/// sites inside `ExprKind::Call` that bypass the end-of-function coerce block.
pub(crate) fn maybe_coerce<'tm>(
    tm: &'tm TermManager,
    term: Term<'tm>,
    coerce_to: &Option<Sort<'tm>>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Result<Term<'tm>, String> {
    let Some(dt_sort) = coerce_to.as_ref() else { return Ok(term); };
    if term.sort() == *dt_sort || !dt_sort.is_dt() || dt_sort.is_tuple() {
        return Ok(term);
    }
    if term.sort().is_integer() || term.sort().is_tuple() || term.sort().is_boolean() {
        return coerce_to_union_dt(tm, term, dt_sort);
    }
    // Distinct-sort term: find the "ck_D_{Name}" constructor in the target DT.
    if let Some((sym, _)) = distinct_preds.iter().find(|(_, i)| i.sort == term.sort()) {
        let ctor_name = format!("ck_D_{}", sym.0);
        let dt = dt_sort.datatype();
        if let Some(ctor) = (0..dt.num_constructors())
            .map(|i| dt.constructor(i))
            .find(|c| c.name() == ctor_name)
        {
            return Ok(tm.mk_term(Kind::ApplyConstructor, &[ctor.term(), term]));
        }
    }
    Ok(term) // sort mismatch but not coercible — caller handles the incompatibility
}

/// SMT sort for a set expression.
///
/// Cross-kind unions (one arm is a tuple, another is a scalar) are now encoded as
/// a CVC5 algebraic datatype with one constructor per arm; `membership_constraint`
/// in `membership.rs` uses `ApplyTester` / `ApplySelector` to check membership.
///
/// For example, `(Nat * Nat) | Nat` becomes a CVC5 datatype:
/// ```text
/// CKU_ck_T_ck_Int_ck_Int_ck_Int {
///   ck_T_ck_Int_ck_Int(f0: Int, f1: Int),
///   ck_Int(f0: Int),
/// }
/// ```
/// with `t ∈ (Nat * Nat) | Nat ↔ (is_ck_T(t) ∧ f0(t) ≥ 0 ∧ f1(t) ≥ 0) ∨ (is_ck_Int(t) ∧ f0(t) ≥ 0)`.
///
/// Every `ExprKind` variant that can appear in set-expression position is listed
/// explicitly.  Adding a new `ExprKind` to the AST will cause a compile error here,
/// forcing a conscious decision about its CVC5 sort rather than silently falling
/// through to integer sort.
pub(crate) fn set_sort<'tm>(
    tm: &'tm TermManager,
    set_expr: &Expr,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<Sort<'tm>> {
    Some(match &set_expr.kind {
        // Bool has its own CVC5 boolean sort.
        ExprKind::Var(sym) if sym.0 == "Bool" => tm.boolean_sort(),
        // Distinct sets each have their own CVC5 uninterpreted sort.
        ExprKind::Var(sym) => {
            if let Some(info) = distinct_preds.get(sym) {
                info.sort.clone()
            } else {
                // All other named sets (Nat, NatPos, Int, Int8…Int64, NonZeroInt, …) → integer.
                tm.integer_sort()
            }
        }
        // Set literals {0}, {1, 2, 3} — elements are integers.
        ExprKind::SetLit(_) => tm.integer_sort(),
        // Comprehensions {x for x in S} — elements are integers.
        ExprKind::Comprehension { .. } => tm.integer_sort(),
        // Built-in set constructors Set(Int), Set(Bool) — variable holds an i64 pointer.
        ExprKind::Call { .. } => tm.integer_sort(),
        // `A * B * C` — Cartesian product → CVC5 tuple sort.
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            let parts = flatten_product(set_expr);
            let sorts: Vec<Sort<'_>> = parts.iter()
                .map(|p| set_sort(tm, p, distinct_preds))
                .collect::<Option<Vec<_>>>()?;
            tm.mk_tuple_sort(&sorts)
        }
        // Set diff (`-`), symmetric diff (`^`), intersection (`&`): always subsets of ℤ.
        ExprKind::BinOp { op: BinOp::Sub | BinOp::SymDiff | BinOp::Intersect, .. } => {
            tm.integer_sort()
        }
        // Union (`|`) and disjoint union (`+`).
        // Cross-kind (tuple arm ∪ scalar, or distinct-sort ∪ anything different)
        // → CVC5 algebraic datatype.
        // Same-kind scalar unions (Bool | Nat, Int | NatPos) → integer sort.
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let ls = set_sort(tm, lhs, distinct_preds)?;
            let rs = set_sort(tm, rhs, distinct_preds)?;
            let is_distinct_sort = |s: &Sort<'_>| distinct_preds.values().any(|i| &i.sort == s);
            if ls.is_tuple() || rs.is_tuple() || ls.is_dt() || rs.is_dt()
                || is_distinct_sort(&ls) || is_distinct_sort(&rs)
            {
                // Cross-kind (tuple, existing DT, or distinct-sort arm): build a
                // CVC5 algebraic datatype with one constructor per arm.
                // Distinct-sort arms get a selector of their uninterpreted sort;
                // all others get integer_sort selectors (one per i64 leaf).
                let arms = flatten_any_union(set_expr);
                return Some(build_union_datatype_sort(tm, &arms, distinct_preds));
            }
            // Both arms are plain scalar (Int-family); integer sort covers both.
            tm.integer_sort()
        }
        // Value-position BinOp operators must not appear in set-expression context.
        ExprKind::BinOp {
            op: BinOp::Div | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le
                | BinOp::Gt | BinOp::Ge | BinOp::And | BinOp::Or
                | BinOp::In | BinOp::NotIn,
            ..
        } => unreachable!(
            "set_sort: value-position BinOp in set-expression context: {:?}",
            set_expr.kind
        ),
        // `X*` — Kleene star: variable-length sequence of X.
        // No fixed CVC5 sort can represent a sequence of unknown length; return None
        // so callers fall back to Unknown rather than creating an incorrect sort.
        // When a concrete tuple body is being range-checked against X*, the term's
        // tuple sort is used directly in membership_constraint without calling set_sort.
        ExprKind::KleeneStar(_) => return None,
        // Value-position ExprKind variants must never appear as set expressions.
        // Listed explicitly so adding a new ExprKind causes a compile error here.
        ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::UnOp { .. }
        | ExprKind::If { .. } | ExprKind::Tuple(_) | ExprKind::Proj { .. }
        | ExprKind::Try(_) | ExprKind::FailLit | ExprKind::FailWith(_) => unreachable!(
            "set_sort: value-position expression in set-expression context: {:?}",
            set_expr.kind
        ),
    })
}

/// Return the success-only arm of a fallible range.
///
/// Strips `Fail` and `Fail * Y` arms from a union, returning the sub-expression
/// that represents the success set.  Used by the `Try` encoding to assert that,
/// after `?` propagation, the result lies in the success set.
///
/// Examples:
///   `Nat | Fail`          → `Some(Nat)`
///   `Nat | (Fail * Y)`    → `Some(Nat)`
///   `Nat | Fail | (Fail * Y)` → `Some(Nat)`
///   `Fail`                → `None`
fn success_arm_of_range(range: &Expr) -> Option<&Expr> {
    fn is_fail_arm(e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            || matches!(
                &e.kind,
                ExprKind::BinOp { op: BinOp::Mul, lhs, .. }
                    if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            )
    }
    if is_fail_arm(range) { return None; }
    if let ExprKind::BinOp { op: BinOp::Union, lhs, rhs } = &range.kind {
        if is_fail_arm(rhs) { return success_arm_of_range(lhs); }
        if is_fail_arm(lhs) { return success_arm_of_range(rhs); }
    }
    Some(range)
}

/// SMT sort for a range expression.
///
/// Strips `Fail` and `Fail * Y` union wrappers to find the success sort,
/// then delegates to `set_sort` (which handles cross-kind unions via datatypes).
pub(crate) fn set_sort_for_range<'tm>(
    tm: &'tm TermManager,
    range: &Expr,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<Sort<'tm>> {
    match &range.kind {
        ExprKind::Var(sym) if sym.0 == "Fail" => Some(tm.integer_sort()),
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            // Strip `Fail * Y` arm — the success sort is the other side.
            let is_fail_product = |e: &Expr| matches!(
                &e.kind,
                ExprKind::BinOp { op: BinOp::Mul, lhs, .. }
                    if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            );
            if is_fail_product(rhs) { return set_sort_for_range(tm, lhs, distinct_preds); }
            if is_fail_product(lhs) { return set_sort_for_range(tm, rhs, distinct_preds); }
            // Non-fail union: delegate to set_sort which handles cross-kind via datatypes.
            set_sort(tm, range, distinct_preds)
        }
        _ => set_sort(tm, range, distinct_preds),
    }
}

/// True if the range (after stripping Fail/Union wrappers) is a product type.
fn is_product_range(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::BinOp { op: BinOp::Mul, .. } => true,
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let is_fail_product = |e: &Expr| matches!(
                &e.kind,
                ExprKind::BinOp { op: BinOp::Mul, lhs, .. }
                    if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            );
            if is_fail_product(rhs) { return is_product_range(lhs); }
            if is_fail_product(lhs) { return is_product_range(rhs); }
            // Non-fail union: no single arm defines the product structure.
            // Previously this silently returned is_product_range(lhs), which caused
            // (Nat * Nat) | Nat to be treated as a product range even though it isn't.
            false
        }
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
