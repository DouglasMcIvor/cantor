//! Expression-level SMT encoding — translating Cantor expressions to cvc5 Terms.

use std::collections::HashMap;

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, UnOp},
    kind::Kind as ValKind,
    semantics::tree::{flatten_cartesian_product, sem_param_set_exprs, SemExpr, SemExprKind, SemFunctionDef, SemFunctionSig},
    span::Symbol,
};

use super::membership::{DistinctPreds, Membership, membership_constraint};
use super::sort::{
    extract_success_value, is_product_range, maybe_coerce, set_sort,
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
pub(crate) fn binary_builtin_domain(op: &BinOp, arg_idx: usize) -> Vec<(SemExpr, &'static str)> {
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
pub(crate) fn unary_builtin_domain(op: &UnOp) -> Vec<(SemExpr, &'static str)> {
    match op {
        // Negation is defined on Int only — distinct sets cannot be negated.
        UnOp::Neg => vec![(named_set("Int"), "operand of negation must be Int, not a member of a distinct set")],
        // Operand of `not` must be in Bool.
        UnOp::Not => vec![(named_set("Bool"), "operand of `not` must be Bool")],
    }
}

/// Build a `Var` expression that refers to a named built-in set.
pub(crate) fn named_set(name: &'static str) -> SemExpr {
    let kind = crate::semantics::builtins::lookup(name).map(|b| b.kind).unwrap_or(crate::kind::Kind::Int);
    SemExpr::var(name, kind)
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
    expr: &SemExpr,
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
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
    if let SemExprKind::Call { callee, args } = &expr.kind {
        // `len(xs)` — the number of elements in a vector (X* value).
        // Encoded as `seq.len(xs)` in the cvc5 sequence theory.
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
                // `Fail` is registered as a distinct sort purely so the
                // cross-kind union machinery treats it like any other arm —
                // it has no user-facing basis value to extract, so `from()`
                // (which unwraps a real `distinct B` back to its `B` basis)
                // must not match it.
                if sym.0 == "Fail" {
                    continue;
                }
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
        SemExprKind::IntLit(n)  => Ok(tm.mk_integer(*n)),
        SemExprKind::BoolLit(b) => Ok(tm.mk_boolean(*b)),

        // `Fail` is a builtin distinct sort (registered in `build_distinct_preds`)
        // with one canonical witness value — the witness is never observed (see
        // the `from()` guard below), so any fixed integer works. `fail` applies
        // the `mk_Fail` constructor directly; `fail expr` pairs it with the
        // payload as a genuine tuple, exactly like any other cross-kind union's
        // payload-carrying arm. The surrounding `coerce_to`/`maybe_coerce`
        // machinery (end of this function) then wraps either shape into the
        // enclosing union datatype with no Fail-specific coercion code at all.
        SemExprKind::FailLit => {
            let info = distinct_preds.get(&Symbol::new("Fail"))
                .expect("Fail must be registered as a builtin distinct sort");
            Ok(tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), tm.mk_integer(0)]))
        }

        SemExprKind::FailWith(inner) => {
            let n = enc!(inner)?;
            let info = distinct_preds.get(&Symbol::new("Fail"))
                .expect("Fail must be registered as a builtin distinct sort");
            let tag = tm.mk_term(Kind::ApplyUf, &[info.mk.clone(), tm.mk_integer(0)]);
            Ok(tm.mk_tuple(&[tag, n]))
        }

        SemExprKind::Var(sym) => {
            if let Some(term) = env.get(sym) {
                Ok(term.clone())
            } else if let Some(def) = name_defs.get(sym) {
                encode_expr(&def.value, &Env::new(), name_defs, fn_env, tm, solver,
                            call_counter, builtin_obligs, path_cond.clone(), distinct_preds, None)
            } else {
                Err(format!("unbound variable `{}`", sym.0))
            }
        }

        SemExprKind::Tuple(elems) => {
            let terms = elems.iter().map(|e| enc!(e)).collect::<Result<Vec<_>, _>>()?;
            Ok(tm.mk_tuple(&terms))
        }

        SemExprKind::UnOp { op, expr: inner } =>
            encode_unop(op, inner, env, name_defs, fn_env, tm, solver,
                        call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        // `+ - * /` are dedicated SemExprKind variants (never wrapped in
        // BinOp — see tree.rs's module doc); route them through the same
        // `encode_binop` that handles the remaining operators, so the
        // domain-obligation logic (Int-only, non-zero divisor, …) isn't
        // duplicated between an arithmetic-only path and the generic one.
        SemExprKind::Add(lhs, rhs) => encode_binop(&BinOp::Add, lhs, rhs, env, name_defs, fn_env, tm, solver,
                                                    call_counter, builtin_obligs, path_cond.clone(), distinct_preds),
        SemExprKind::Sub(lhs, rhs) => encode_binop(&BinOp::Sub, lhs, rhs, env, name_defs, fn_env, tm, solver,
                                                    call_counter, builtin_obligs, path_cond.clone(), distinct_preds),
        SemExprKind::Mul(lhs, rhs) => encode_binop(&BinOp::Mul, lhs, rhs, env, name_defs, fn_env, tm, solver,
                                                    call_counter, builtin_obligs, path_cond.clone(), distinct_preds),
        SemExprKind::Div(lhs, rhs) => encode_binop(&BinOp::Div, lhs, rhs, env, name_defs, fn_env, tm, solver,
                                                    call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        SemExprKind::BinOp { op, lhs, rhs } =>
            encode_binop(op, lhs, rhs, env, name_defs, fn_env, tm, solver,
                         call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        SemExprKind::If { cond, then_expr, else_expr } =>
            encode_if(cond, then_expr, else_expr, env, name_defs, fn_env, tm, solver,
                      call_counter, builtin_obligs, path_cond.clone(), distinct_preds,
                      coerce_to.clone()),

        SemExprKind::Call { callee, args } =>
            encode_call(callee, args, env, name_defs, fn_env, tm, solver,
                        call_counter, builtin_obligs, path_cond.clone(), distinct_preds,
                        coerce_to.clone(), false),

        // `f(args)?` — on the success path the result lies in the success arm
        // of the callee's range. That narrowing is only valid for a signature
        // whose domain the arguments actually satisfy, so it is asserted
        // per-signature as `args ∈ domain_i → result ∈ success_arm(range_i)`
        // inside `encode_call` (`narrow_try`), never unconditionally — an
        // unguarded assertion would let an out-of-domain or other-overload
        // call "prove" the wrong success set.
        SemExprKind::Try(inner) => match &inner.kind {
            SemExprKind::Call { callee, args } =>
                encode_call(callee, args, env, name_defs, fn_env, tm, solver,
                            call_counter, builtin_obligs, path_cond.clone(), distinct_preds,
                            None, true),
            _ => enc!(inner),
        },

        SemExprKind::Proj { base, index } =>
            encode_proj(base, *index, env, name_defs, fn_env, tm, solver,
                        call_counter, builtin_obligs, path_cond.clone(), distinct_preds),

        SemExprKind::Index { base, index } => {
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

        SemExprKind::SetLit(_) | SemExprKind::Comprehension { .. } | SemExprKind::KleeneStar(_) =>
            Err("set expressions cannot appear in value position \
                 (only in domain/range/`in`/`for` positions)".into()),

        // Set-position-only variants: elaboration never threads these into a
        // value-position tree (see `semantics::elaborate`'s module doc), so
        // reaching them here means an elaborator invariant broke.
        SemExprKind::DisjointUnion(..) | SemExprKind::SetDifference(..)
        | SemExprKind::CartesianProduct(..) | SemExprKind::SetQuotient(..) =>
            Err(format!(
                "elaborator invariant broken: set-position node {:?} reached encode_expr \
                 (value position)", expr.kind
            )),
    }?;

    maybe_coerce(tm, term, &coerce_to)
}

// ── Arm helpers ───────────────────────────────────────────────────────────────

fn encode_unop<'tm>(
    op: &UnOp,
    inner: &SemExpr,
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
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
    Err("`++` requires vector (X*) operands; operand is not a sequence or array literal".into())
}

fn encode_binop<'tm>(
    op: &BinOp,
    lhs: &SemExpr,
    rhs: &SemExpr,
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
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
            if let SemExprKind::Var(sym) = &rhs.kind {
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
            if let SemExprKind::Var(sym) = &rhs.kind {
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
        let l_seq = coerce_to_sequence(tm, l.clone())?;
        let r_seq = coerce_to_sequence(tm, r.clone())?;
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

    // `==`/`!=` between different solver sorts would be an ill-sorted CVC5
    // term (process abort). Elaboration already rejects cross-kind operands;
    // what reaches here is same-Kind-different-sort — e.g. a distinct-set
    // value against its basis (`litre(3) == 3`), where the honest answer is
    // Unknown until distinct equality is modelled explicitly.
    if matches!(op, BinOp::Eq | BinOp::Ne) && l.sort() != r.sort() {
        return Err(format!(
            "cannot encode `{op:?}` between values with different solver \
             representations (e.g. a distinct-set value and its basis) — \
             unwrap with from() first"
        ));
    }

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
    cond: &SemExpr,
    then_expr: &SemExpr,
    else_expr: &SemExpr,
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
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
    //
    // The common case where branches differ only because one is `fail`/
    // `fail n` (e.g. `if cond then 5 else fail` with range `Nat | Fail`) is
    // already handled above: `coerce_to` is propagated into both branches,
    // and each one's own `maybe_coerce` independently wraps it into the
    // enclosing union datatype (`Fail` is just another arm — see
    // docs/design-decisions.md §13), so `t.sort() == e.sort()` already holds
    // by the time we get here. There is no Fail-specific coercion left to do
    // in this function at all.
    let (t, e) = if t.sort() == e.sort() {
        (t, e)
    } else {
        // Branches have genuinely different sorts and cannot be unified —
        // Bool and Int are disjoint in Cantor's value model (no implicit
        // 0/1 coercion; write `if b then 1 else 0` to convert explicitly),
        // and anything else (distinct sort, tuple, future Float32, …) is no
        // more compatible. In practice `elaborate()` already rejects
        // mismatched non-Tuple/TaggedUnion branch Kinds for a legitimate
        // program (see `kind::merge_if_branches`), and any Fail-vs-success
        // mismatch should already have been unified via `coerce_to` above —
        // so reaching this arm at all means either an elaborator gap or a
        // missing `coerce_to` (e.g. a `let`/`:=` RHS, which doesn't thread
        // one through today). This is a defensive fallback, not a supported
        // path: for whichever branch isn't integer-sorted, push a
        // path-conditioned `false` obligation (that branch's value can never
        // satisfy an integer-shaped range) and substitute a dummy integer so
        // `Ite` stays well-sorted — a sound under-approximation, never a
        // silent pass.
        let mut to_int_or_dummy = |b: Term<'tm>, path: Term<'tm>| {
            if b.sort().is_integer() {
                b
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
    args: &[SemExpr],
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    call_counter: &mut usize,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
    path_cond: Term<'tm>,
    distinct_preds: &DistinctPreds<'tm>,
    coerce_to: Option<Sort<'tm>>,
    // True when this call sits directly under `?`: additionally assert the
    // per-signature success-narrowing `args ∈ domain_i → result ∈ success_arm_i`.
    narrow_try: bool,
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

    push_call_domain_obligation(
        callee, callee_def, args, &arg_terms, tm, name_defs, distinct_preds,
        &path_cond, builtin_obligs,
    )?;

    let fresh = format!("_call_{}", *call_counter);
    *call_counter += 1;

    // For tuple-returning callees, decompose the result into leaf scalar
    // constants assembled with mk_tuple — same reason as for tuple params:
    // a symbolic tuple constant can't be used with child() extraction.
    let result_var = if let Some(first_sig) = callee_def.sigs.first() {
        if is_product_range(&first_sig.range) {
            let (assembled, leaves) = mk_decomposed_tuple(tm, &fresh, &first_sig.range, distinct_preds, name_defs);
            for (leaf, leaf_set) in leaves {
                if let Membership::Constrained(c) =
                    membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds)
                {
                    solver.assert_formula(c);
                }
            }
            assembled
        } else {
            match set_sort(tm, &first_sig.range, distinct_preds, name_defs) {
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
        if narrow_try {
            if let Some(success) = success_arm_of_range(&sig.range) {
                assert_domain_implies_membership(
                    sig, &arg_terms, result_var.clone(), success, tm, solver, name_defs, distinct_preds,
                );
            }
        }
    }

    if narrow_try {
        // `result_var` is sorted as the *whole* range (a cross-kind datatype
        // whenever the range has a Fail-shaped arm — always, now that `Fail`
        // is a distinct sort). `?` must yield just the success value, not the
        // tagged wrapper — callers immediately use it as a plain Int/Bool/
        // tuple value (e.g. `y : Nat = f(x)?; y - 1`), which would otherwise
        // build an ill-sorted term against `result_var`'s DT sort.
        let first_sig = callee_def.sigs.first().ok_or_else(|| {
            format!("call to `{}` under `?` has no signature (internal error)", callee.0)
        })?;
        let success = success_arm_of_range(&first_sig.range).ok_or_else(|| format!(
            "`?` used on a call to `{}`, whose range has no success arm to narrow to",
            callee.0
        ))?;
        return extract_success_value(tm, result_var, success, distinct_preds, name_defs).ok_or_else(|| format!(
            "cannot narrow `?` on call to `{}`: the success arm's shape doesn't \
             resolve to a single extraction from its range's datatype",
            callee.0
        ));
    }

    Ok(result_var)
}

// ── Call-site domain obligation ───────────────────────────────────────────────

/// How one callee signature relates to the arguments of a specific call.
enum DomainMatch<'tm> {
    /// The signature's arity cannot cover this call — it contributes nothing.
    Mismatch,
    /// The domain imposes no constraint on these arguments (e.g. all `Int`
    /// parts against integer-sorted terms) — the obligation is trivially met.
    Trivial,
    /// The arguments belong to this signature's domain iff this term holds.
    Constrained(Term<'tm>),
}

fn sig_domain_match<'tm>(
    sig: &SemFunctionSig,
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    callee: &Symbol,
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
) -> Result<DomainMatch<'tm>, String> {
    let parts = match sem_param_set_exprs(sig.domain.as_ref(), arg_terms.len()) {
        Ok(p) => p,
        Err(_) => return Ok(DomainMatch::Mismatch),
    };
    let mut conjuncts: Vec<Term<'_>> = Vec::new();
    for ((arg, term), part) in args.iter().zip(arg_terms).zip(&parts) {
        // Vector-let / runtime-set bindings are opaque integer constants in the
        // solver; a membership constraint built on the raw pointer term would be
        // meaningless (and the scalar-lift path would read it as a length-1
        // sequence). Unknown is the only honest answer until they are value-encoded.
        if matches!(arg.kind_of, ValKind::Vector(_) | ValKind::Set(_)) && term.sort().is_integer() {
            return Err(format!(
                "cannot verify call to `{}`: argument `{}` is an opaque runtime \
                 value the solver does not yet value-encode",
                callee.0, arg
            ));
        }
        match membership_constraint(tm, term.clone(), part, name_defs, distinct_preds) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => conjuncts.push(c),
            Membership::Unsupported => return Err(format!(
                "cannot verify call to `{}`: domain `{}` uses syntax not yet \
                 supported in the SMT encoding",
                callee.0, part
            )),
        }
    }
    Ok(match conjuncts.len() {
        0 => DomainMatch::Trivial,
        1 => DomainMatch::Constrained(conjuncts.remove(0)),
        _ => DomainMatch::Constrained(tm.mk_term(Kind::And, &conjuncts)),
    })
}

/// Push the proof obligation that the call's arguments lie in the domain of
/// at least one of the callee's declared signatures.
///
/// Without this obligation the per-signature contracts are vacuous
/// implications: an out-of-domain call (e.g. passing `0` where the domain is
/// `Int - {0}`) would simply fail every antecedent, the callee's body — proved
/// only *under* its domain assumption — would be entered with an input it was
/// never verified against, and the caller would still be reported `proved`.
fn push_call_domain_obligation<'tm>(
    callee: &Symbol,
    callee_def: &SemFunctionDef,
    args: &[SemExpr],
    arg_terms: &[Term<'tm>],
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
    path_cond: &Term<'tm>,
    builtin_obligs: &mut Vec<BuiltinObligation<'tm>>,
) -> Result<(), String> {
    let mut arms: Vec<Term<'_>> = Vec::new();
    for sig in &callee_def.sigs {
        match sig_domain_match(sig, args, arg_terms, callee, tm, name_defs, distinct_preds)? {
            DomainMatch::Mismatch => {}
            DomainMatch::Trivial => return Ok(()),
            DomainMatch::Constrained(c) => arms.push(c),
        }
    }
    let (obligation, reason) = if arms.is_empty() {
        (
            tm.mk_boolean(false),
            format!("no signature of `{}` accepts {} argument(s)", callee.0, arg_terms.len()),
        )
    } else if arms.len() == 1 {
        (
            arms.remove(0),
            format!("arguments to `{}` are not in its declared domain", callee.0),
        )
    } else {
        (
            tm.mk_term(Kind::Or, &arms),
            format!("arguments to `{}` do not satisfy any of its declared domains", callee.0),
        )
    };
    builtin_obligs.push(BuiltinObligation {
        path_cond: path_cond.clone(),
        obligation,
        violated_reason: reason,
    });
    Ok(())
}

fn encode_proj<'tm>(
    base: &SemExpr,
    index: usize,
    env: &Env<'tm>,
    name_defs: &NameDefs,
    fn_env: &HashMap<Symbol, &SemFunctionDef>,
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
/// (The call-site *obligation* that the args actually satisfy some domain is
/// separate — see `push_call_domain_obligation`.)
pub(crate) fn assert_call_contract<'tm>(
    sig: &SemFunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
) {
    assert_domain_implies_membership(sig, arg_terms, result, &sig.range, tm, solver, name_defs, distinct_preds);
}

/// Assert `args ∈ sig.domain → result ∈ target_set` as a solver fact.
///
/// Used for both the full call contract (`target_set` = the range) and the
/// `?` success-narrowing (`target_set` = the range's success arm). Arity is
/// matched with the same tuple-vs-scalars rule as parameter binding
/// (`sem_param_set_exprs`); a signature that can't cover this call, or any
/// unsupported membership, skips the fact — fewer facts, never wrong ones.
fn assert_domain_implies_membership<'tm>(
    sig: &SemFunctionSig,
    arg_terms: &[Term<'tm>],
    result: Term<'tm>,
    target_set: &SemExpr,
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
) {
    let parts = match sem_param_set_exprs(sig.domain.as_ref(), arg_terms.len()) {
        Ok(p) => p,
        Err(_) => return,
    };
    let mut antecedents: Vec<Term<'_>> = Vec::new();
    for (part, arg) in parts.iter().zip(arg_terms.iter()) {
        match membership_constraint(tm, arg.clone(), part, name_defs, distinct_preds) {
            Membership::Unconstrained => {}
            Membership::Constrained(c) => antecedents.push(c),
            Membership::Unsupported => return,
        }
    }

    let consequent = match membership_constraint(tm, result, target_set, name_defs, distinct_preds) {
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
pub(crate) fn proj_from_tuple<'tm>(tm: &'tm TermManager, base: Term<'tm>, index: usize) -> Result<Term<'tm>, String> {
    let sel = base.sort().datatype().constructor(0).selector(index);
    Ok(tm.mk_term(Kind::ApplySelector, &[sel.term(), base]))
}

/// Number of elements in a tuple-sorted term, read from its sort's datatype —
/// works for any tuple-sorted term, not just genuine `mk_tuple(...)` constructor
/// applications (an opaque SSA constant carrying a tuple sort has no children,
/// but its sort still knows its own arity).
pub(crate) fn tuple_arity<'tm>(base: &Term<'tm>) -> usize {
    base.sort().datatype().constructor(0).num_selectors()
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
    set_expr: &'e SemExpr,
    distinct_preds: &DistinctPreds<'tm>,
    name_defs: &NameDefs,
) -> (Term<'tm>, Vec<(Term<'tm>, &'e SemExpr)>) {
    let parts = flatten_cartesian_product(set_expr);
    if parts.len() <= 1 {
        let sort = set_sort(tm, set_expr, distinct_preds, name_defs)
            .expect("mk_decomposed_tuple: leaf set expression has no representable CVC5 sort");
        let leaf = tm.mk_const(sort, name);
        return (leaf.clone(), vec![(leaf, set_expr)]);
    }
    let mut leaves = Vec::new();
    let mut child_terms = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        let child_name = format!("{name}__{i}");
        let (child_term, child_leaves) = mk_decomposed_tuple(tm, &child_name, part, distinct_preds, name_defs);
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
    name_defs: &'a NameDefs,
) -> Option<&'a crate::semantics::tree::SemNameDef> {
    use crate::ast::DefKind;
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    let sym = Symbol::new(capitalized);
    name_defs.get(&sym).filter(|def| def.kind == DefKind::Distinct).map(|def| def)
}
