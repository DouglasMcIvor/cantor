//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind, FunctionDef, FunctionSig, UnOp},
    span::{Span, Symbol},
};

use super::membership::{DistinctPreds, Membership, membership_constraint};
use super::sort::{
    flatten_product, is_product_range, maybe_coerce, set_sort, set_sort_for_range,
    success_arm_of_range,
};
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
        // ── Vector operations ─────────────────────────────────────────────────
        // `++` operands must be vectors; their element sorts are checked by CVC5.
        (BinOp::Concat, _) => vec![],
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

// ── Expression encoder (compact router) ──────────────────────────────────────

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
///
/// `coerce_to`: when `Some(sort)`, coerce integer/boolean/tuple-sorted results
/// to that union datatype sort.  Used to unify cross-kind union if/else branches
/// so both arms have the same CVC5 sort before `Ite` is applied.
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
    coerce_to: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, path_cond.clone(), distinct_preds, None)
        };
    }

    // `size()`, `from()`, and `len()` are built-in call builtins that bypass the
    // final maybe_coerce (they return predicates / unwrapped scalars, not union values).
    if let ExprKind::Call { callee, args } = &expr.kind {
        // `len(xs)` — the number of elements in a vector (X* value).
        // Encoded as `seq.len(xs)` in the cvc5 sequence theory.
        // TODO: if/when arrays get codegen, also support `len` on fixed-length tuples.
        if callee.0 == "len" && args.len() == 1 {
            let arg_term = enc!(&args[0])?;
            if !arg_term.sort().is_sequence() {
                return Err(
                    "len() expects a vector (X*) argument; \
                     use it only on Kleene-star values".into()
                );
            }
            return Ok(tm.mk_term(Kind::SeqLength, &[arg_term]));
        }
        if callee.0 == "size" && args.len() == 1 {
            let fresh = format!("_size_{}", *call_counter);
            *call_counter += 1;
            let result = tm.mk_const(tm.integer_sort(), &fresh);
            let non_neg = tm.mk_term(Kind::Geq, &[result.clone(), tm.mk_integer(0)]);
            solver.assert_formula(non_neg);
            return Ok(result);
        }
        if callee.0 == "from" && args.len() == 1 {
            let arg_term = enc!(&args[0])?;
            for (sym, info) in distinct_preds {
                if arg_term.sort() == info.sort {
                    let result = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), arg_term]);
                    if let Some(def) = name_defs.get(sym) {
                        if let Membership::Constrained(c) =
                            membership_constraint(tm, result.clone(), &def.value, name_defs, distinct_preds)
                        {
                            solver.assert_formula(c);
                        }
                    }
                    return Ok(result);
                }
            }
            return Err("from() applied to a value that is not a member of any distinct set".into());
        }
    }

    let term = match &expr.kind {
        ExprKind::IntLit(n)  => Ok(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Ok(tm.mk_boolean(*b)),
        ExprKind::FailLit    => Ok(tm.mk_integer(i64::MIN)),

        ExprKind::FailWith(inner) => {
            let n = enc!(inner)?;
            Ok(tm.mk_term(Kind::Add, &[tm.mk_integer(i64::MIN.wrapping_add(1)), n]))
        }

        ExprKind::Var(sym) => {
            if let Some(term) = env.get(sym) {
                Ok(term.clone())
            } else if let Some(def) = name_defs.get(sym) {
                encode_expr(&def.value, &Env::new(), name_defs, fn_env, tm, solver,
                            call_counter, builtin_obligs, path_cond.clone(), distinct_preds, None)
            } else {
                Err(format!("unbound variable `{}`", sym.0))
            }
        }

        ExprKind::Tuple(elems) => {
            let terms = elems.iter().map(|e| enc!(e)).collect::<Result<Vec<_>, _>>()?;
            Ok(tm.mk_tuple(&terms))
        }

        ExprKind::UnOp { op, expr: inner } =>
            encode_unop(op, inner, env, name_defs, fn_env, tm, solver,
                        call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        ExprKind::BinOp { op, lhs, rhs } =>
            encode_binop(op, lhs, rhs, env, name_defs, fn_env, tm, solver,
                         call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        ExprKind::If { cond, then_expr, else_expr } =>
            encode_if(cond, then_expr, else_expr, env, name_defs, fn_env, tm, solver,
                      call_counter, builtin_obligs, path_cond.clone(), distinct_preds,
                      coerce_to.clone()),

        ExprKind::Call { callee, args } =>
            encode_call(callee, args, env, name_defs, fn_env, tm, solver,
                        call_counter, builtin_obligs, path_cond.clone(), distinct_preds,
                        coerce_to.clone()),

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

        ExprKind::Proj { base, index } =>
            encode_proj(base, *index, env, name_defs, fn_env, tm, solver,
                        call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        ExprKind::Index { base, index } => {
            let base_term = enc!(base)?;
            let idx_term  = enc!(index)?;
            if !base_term.sort().is_sequence() {
                return Err("runtime index `xs[i]` is only valid on vector (X*) values".into());
            }
            // Push a bounds obligation for all vector indexing: the solver tracks
            // whether `0 ≤ i < len(xs)` is provable.  Scalar element sorts (Int /
            // Bool) have benign out-of-bounds defaults (0 / false), so this is
            // technically optional for them but keeps the model correct.  For tuple
            // element sorts (struct vecs) it is essential: CVC5 can assign arbitrary
            // default components that fall outside the element range, producing false
            // counterexamples without this obligation.
            let len = tm.mk_term(Kind::SeqLength, &[base_term.clone()]);
            let lo = tm.mk_term(Kind::Leq, &[tm.mk_integer(0), idx_term.clone()]);
            let hi = tm.mk_term(Kind::Lt,  &[idx_term.clone(), len]);
            builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: tm.mk_term(Kind::And, &[lo, hi]),
                violated_reason: "vector index may be out of bounds".into(),
            });
            Ok(tm.mk_term(Kind::SeqNth, &[base_term, idx_term]))
        }

        ExprKind::SetLit(_) | ExprKind::Comprehension { .. } | ExprKind::KleeneStar(_) =>
            Err("set expressions cannot appear in value position \
                 (only in domain/range/`in`/`for` positions)".into()),
    }?;

    maybe_coerce(tm, term, &coerce_to)
}

// ── Arm helpers ───────────────────────────────────────────────────────────────

fn encode_unop<'tm>(
    op: &UnOp,
    inner: &Expr,
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
    let t = encode_expr(inner, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, path_cond.clone(), distinct_preds, None)?;
    for (domain, reason) in unary_builtin_domain(op) {
        if let Membership::Constrained(c) =
            membership_constraint(tm, t.clone(), &domain, name_defs, distinct_preds)
        {
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

/// Coerce a cvc5 term to sequence sort for use with `SeqConcat`.
///
/// If `term` is already sequence-sorted, return it unchanged.
/// If `term` is tuple-sorted (from an array literal like `[1, 2, 3]`),
/// convert it by wrapping each element in `SeqUnit` and concatenating.
/// Otherwise return an error: `++` only works on vector (X*) values.
fn coerce_to_sequence<'tm>(
    tm: &'tm TermManager,
    term: Term<'tm>,
    original_expr: &Expr,
) -> Result<Term<'tm>, String> {
    if term.sort().is_sequence() {
        return Ok(term);
    }
    if term.sort().is_tuple() {
        let dt = term.sort().datatype();
        let n_elems = dt.constructor(0).num_selectors();
        if n_elems == 0 {
            // Empty tuple [] → empty sequence.  Element sort must be inferred from
            // context; we use integer as the fallback since `[]` only makes sense
            // for a known element-sort vector — the solver will constrain further.
            return Ok(tm.mk_empty_sequence(tm.integer_sort()));
        }
        // Non-empty: fold SeqUnit(elem_i) with SeqConcat.
        let ctor = dt.constructor(0);
        let first_sel = ctor.selector(0);
        let first_elem = tm.mk_term(Kind::ApplySelector, &[first_sel.term(), term.clone()]);
        let mut seq = tm.mk_term(Kind::SeqUnit, &[first_elem]);
        for i in 1..n_elems {
            let sel = ctor.selector(i);
            let elem = tm.mk_term(Kind::ApplySelector, &[sel.term(), term.clone()]);
            let unit = tm.mk_term(Kind::SeqUnit, &[elem]);
            seq = tm.mk_term(Kind::SeqConcat, &[seq, unit]);
        }
        return Ok(seq);
    }
    let _ = original_expr;
    Err("`++` requires vector (X*) operands; operand is not a sequence or array literal".into())
}

fn encode_binop<'tm>(
    op: &BinOp,
    lhs: &Expr,
    rhs: &Expr,
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
            encode_expr($e, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, path_cond.clone(), distinct_preds, None)
        };
    }

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
                Membership::Constrained(c) => Ok(c),
                Membership::Unconstrained  => Ok(tm.mk_boolean(true)),
                Membership::Unsupported    => Err("unsupported set in `in` expression".into()),
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
                Membership::Constrained(c) => Ok(tm.mk_term(Kind::Not, &[c])),
                Membership::Unconstrained  => Ok(tm.mk_boolean(false)),
                Membership::Unsupported    => Err("unsupported set in `not in` expression".into()),
            };
        }
        _ => {}
    }

    let l = enc!(lhs)?;
    let r = enc!(rhs)?;

    for (arg_idx, arg_term) in [&l, &r].iter().enumerate() {
        for (domain, reason) in binary_builtin_domain(op, arg_idx) {
            if let Membership::Constrained(c) =
                membership_constraint(tm, (*arg_term).clone(), &domain, name_defs, distinct_preds)
            {
                builtin_obligs.push(BuiltinObligation {
                    path_cond: path_cond.clone(),
                    obligation: c,
                    violated_reason: reason.to_string(),
                });
            }
        }
    }

    // `xs ++ ys` — vector concatenation.  Both operands must be sequence-sorted.
    // If either is a tuple (from an array literal), coerce it to a sequence first.
    if *op == BinOp::Concat {
        let l_seq = coerce_to_sequence(tm, l.clone(), lhs)?;
        let r_seq = coerce_to_sequence(tm, r.clone(), rhs)?;
        return Ok(tm.mk_term(Kind::SeqConcat, &[l_seq, r_seq]));
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
        BinOp::Concat => unreachable!("handled above"),
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

fn encode_if<'tm>(
    cond: &Expr,
    then_expr: &Expr,
    else_expr: &Expr,
    env: &Env<'tm>,
    name_defs: &NameDefs<'_>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    path_cond: Term<'tm>,
    distinct_preds: &DistinctPreds<'tm>,
    coerce_to: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    let c = encode_expr(cond, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, path_cond.clone(), distinct_preds, None)?;

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
    let t = encode_expr(then_expr, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, then_guard, distinct_preds, coerce_to.clone())?;

    // Else-branch: path_cond ∧ ¬cond
    let not_c = tm.mk_term(Kind::Not, &[c_bool.clone()]);
    let else_guard = tm.mk_term(Kind::And, &[path_cond.clone(), not_c]);
    let e = encode_expr(else_expr, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, else_guard, distinct_preds, coerce_to.clone())?;

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
                    violated_reason: "branch value's set cannot satisfy the range".to_string(),
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

fn encode_call<'tm>(
    callee: &Symbol,
    args: &[Expr],
    env: &Env<'tm>,
    name_defs: &NameDefs<'_>,
    fn_env: &HashMap<Symbol, &FunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    path_cond: Term<'tm>,
    distinct_preds: &DistinctPreds<'tm>,
    coerce_to: Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    macro_rules! enc {
        ($e:expr) => {
            encode_expr($e, env, name_defs, fn_env, tm, solver, call_counter,
                        builtin_obligs, path_cond.clone(), distinct_preds, None)
        };
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
                    Membership::Unconstrained | Membership::Unsupported => {}
                }
                let result = tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), arg_term]);
                // maybe_coerce handles distinct→DT coercion; router's final call is a no-op.
                return maybe_coerce(tm, result, &coerce_to);
            }
        }
    }

    let arg_terms: Vec<Term<'_>> = args.iter().map(|a| enc!(a)).collect::<Result<_, _>>()?;

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
                if let Membership::Constrained(c) =
                    membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds)
                {
                    solver.assert_formula(c);
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

fn encode_proj<'tm>(
    base: &Expr,
    index: usize,
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
    let base_term = encode_expr(base, env, name_defs, fn_env, tm, solver, call_counter,
                                builtin_obligs, path_cond.clone(), distinct_preds, None)?;

    // Struct vector indexing: `xs.N` / `xs[N]` on a sequence-sorted term.
    // (e.g. `(Nat * Nat)*` encoded as `Seq(Tuple(Int, Int))`).
    // Encode as SeqNth(xs, N) and push a bounds obligation (N < len(xs)).
    // The result has the element sort (e.g. Tuple(Int, Int)); the caller's
    // outer Proj, if any, lands on a tuple-sorted term that ApplySelector handles.
    if base_term.sort().is_sequence() {
        let idx_term = tm.mk_integer(index as i64);
        let nth = tm.mk_term(Kind::SeqNth, &[base_term.clone(), idx_term.clone()]);
        let len = tm.mk_term(Kind::SeqLength, &[base_term]);
        let in_bounds = tm.mk_term(Kind::Lt, &[idx_term, len]);
        builtin_obligs.push(BuiltinObligation {
            path_cond: path_cond.clone(),
            obligation: in_bounds,
            violated_reason: format!("vector index {index} may be out of bounds"),
        });
        return Ok(nth);
    }

    // CVC5 tuple sorts also satisfy is_dt() == true; we only want the
    // special-case path for cross-kind union DTs (non-tuple algebraic
    // datatypes built by build_union_datatype_sort).
    if base_term.sort().is_dt() && !base_term.sort().is_tuple() {
        // Find a tuple arm (constructor names start with "ck_T_") that has
        // enough fields for this projection index.
        let dt = base_term.sort().datatype();
        let tuple_ctor = (0..dt.num_constructors())
            .map(|i| dt.constructor(i))
            .find(|c| c.name().starts_with("ck_T_") && c.num_selectors() > index);

        return if let Some(ctor) = tuple_ctor {
            // Push a tester obligation: the value must be in the tuple arm.
            // If the solver finds a valuation where it is in the scalar arm,
            // it reports a counterexample.
            let tester = tm.mk_term(Kind::ApplyTester, &[ctor.tester_term(), base_term.clone()]);
            builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: tester,
                violated_reason: format!(
                    "projection `.{}` requires the value to be in the tuple arm; \
                     the scalar arm of the union would make this invalid",
                    index
                ),
            });
            // ApplySelector is arithmetic-safe (unlike TupleProject) and
            // works on symbolic DT terms, including Ite results.
            let sel = ctor.selector(index);
            Ok(tm.mk_term(Kind::ApplySelector, &[sel.term(), base_term]))
        } else {
            // No tuple arm with enough fields: projection is always invalid.
            builtin_obligs.push(BuiltinObligation {
                path_cond: path_cond.clone(),
                obligation: tm.mk_boolean(false),
                violated_reason: format!(
                    "projection `.{}` on a cross-kind union with no matching tuple arm",
                    index
                ),
            });
            Ok(tm.mk_integer(0))
        };
    }

    proj_from_tuple(tm, base_term, index)
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

// ── Value extraction helpers ──────────────────────────────────────────────────

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

// ── Tuple projection helpers ──────────────────────────────────────────────────

/// Project field `index` from a tuple-sorted CVC5 term.
///
/// Uses `ApplySelector` rather than `child(index + 1)` so this works for any
/// tuple-sorted term: concrete `mk_tuple(a, b, c)` applications, `Ite` results,
/// and `SeqNth` results (which are symbolic, not `APPLY_CONSTRUCTOR` terms).
fn proj_from_tuple<'tm>(tm: &'tm TermManager, base: Term<'tm>, index: usize) -> Result<Term<'tm>, String> {
    let sel = base.sort().datatype().constructor(0).selector(index);
    Ok(tm.mk_term(Kind::ApplySelector, &[sel.term(), base]))
}

/// Create a decomposed representation of a tuple-valued term.
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

// ── Distinct-set helpers ──────────────────────────────────────────────────────

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
