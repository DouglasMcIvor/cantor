//! Set membership encoding — mapping Cantor set expressions to cvc5 predicates.

use std::collections::HashMap;

use cvc5::{Kind, Sort, Term, TermManager};

use crate::ast::{BinOp, DefKind, Expr, ExprKind, UnOp};
use crate::span::Symbol;

use super::sort::{arm_ctor_name_for_arm, flatten_any_union, flatten_product};
use super::NameDefs;

/// Per-distinct-set CVC5 artefacts created when `D = distinct B` is declared.
///
/// Each distinct set gets its own opaque CVC5 uninterpreted sort so the solver
/// cannot confuse values of different distinct sets or of their basis.
pub(crate) struct DistinctInfo<'tm> {
    /// Opaque CVC5 sort — every D-value has this sort.
    pub(crate) sort: Sort<'tm>,
    /// Constructor UF: `mk_D : Int → D_sort`.
    /// Applying `mk_D(n)` wraps the integer `n` as a D-value.
    pub(crate) mk:   Term<'tm>,
    /// Destructor UF: `from_D : D_sort → Int`.
    /// Applying `from_D(x)` extracts the underlying integer from a D-value.
    pub(crate) from: Term<'tm>,
}

/// Map from distinct set name to its CVC5 encoding artefacts.
pub(crate) type DistinctPreds<'tm> = HashMap<Symbol, DistinctInfo<'tm>>;

/// The result of asking "what does `t ∈ set_expr` look like as a cvc5 term?"
pub(crate) enum Membership<'tm> {
    /// The set is ℤ — every integer qualifies; no assertion needed.
    Unconstrained,
    /// A concrete cvc5 predicate that holds iff `t` is in the set.
    Constrained(Term<'tm>),
    /// The set expression uses syntax we don't yet encode.
    Unsupported,
}

/// Evaluate a constant integer expression to an `i64`, or return `None` if
/// the expression is not a compile-time constant.  Handles `IntLit` and
/// `UnOp::Neg` so that set literals like `{-1}` work correctly (the parser
/// emits `-1` as `Neg(IntLit(1))`, not as `IntLit(-1)`).
fn eval_const_int(expr: &Expr) -> Option<i64> {
    match &expr.kind {
        ExprKind::IntLit(n) => Some(*n),
        ExprKind::UnOp { op: UnOp::Neg, expr: inner } => eval_const_int(inner).map(|n| -n),
        _ => None,
    }
}

/// Coerce a cvc5 term to integer sort for use in arithmetic membership constraints.
///
/// In Cantor's model every value has an integer representation: integers pass
/// through unchanged; booleans are encoded as 0 (false) or 1 (true).  Any
/// other sort (e.g. a CVC5 tuple sort) cannot be represented as an integer —
/// such a term can never be a member of any scalar (integer-valued) set, so
/// callers should return `Constrained(false)` when this returns `None`.
fn to_integer_term<'tm>(tm: &'tm TermManager, t: Term<'tm>) -> Option<Term<'tm>> {
    if t.sort().is_integer() {
        Some(t)
    } else if t.sort().is_boolean() {
        // Bool = {false=0, true=1}: represent as the integer 0 or 1.
        Some(tm.mk_term(Kind::Ite, &[t, tm.mk_integer(1), tm.mk_integer(0)]))
    } else {
        None
    }
}

/// Membership predicate for a term whose CVC5 sort is an algebraic datatype.
///
/// This handles cross-kind union values: `t ∈ set_expr` where `t` was created
/// from a `Kind::TaggedUnion` domain via `set_sort` (which returns a CVC5
/// datatype sort).  The set expression is flattened into its union arms and for
/// each arm we emit `is_ArmN(t) ∧ field_constraints`.
///
/// Selectors match the declaration order in `build_union_datatype_sort`:
/// one `integer_sort` selector `f{j}` per i64 leaf of the arm's kind.
fn membership_constraint_for_dt<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set_expr: &Expr,
    name_defs: &NameDefs<'_>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Membership<'tm> {
    let dt = t.sort().datatype();
    let arm_exprs = flatten_any_union(set_expr);

    let mut disjuncts: Vec<Term<'_>> = Vec::new();
    for arm_expr in arm_exprs {
        let ctor_name = arm_ctor_name_for_arm(arm_expr, distinct_preds);

        // Find the constructor by name — if not present, this arm can't match.
        let ctor = (0..dt.num_constructors())
            .map(|i| dt.constructor(i))
            .find(|c| c.name() == ctor_name);
        let Some(ctor) = ctor else { continue; };

        let tester = tm.mk_term(Kind::ApplyTester, &[ctor.tester_term(), t.clone()]);
        let mut conjuncts: Vec<Term<'_>> = vec![tester];

        // Field constraints: check each leaf selector against the arm's set.
        match &arm_expr.kind {
            ExprKind::BinOp { op: BinOp::Mul, .. } => {
                // Tuple arm: one selector per product component.
                let parts = flatten_product(arm_expr);
                for (j, part) in parts.iter().enumerate() {
                    let sel = ctor.selector(j);
                    let field = tm.mk_term(Kind::ApplySelector, &[sel.term(), t.clone()]);
                    match membership_constraint(tm, field, part, name_defs, distinct_preds) {
                        Membership::Constrained(c) => conjuncts.push(c),
                        Membership::Unconstrained => {}
                        Membership::Unsupported => return Membership::Unsupported,
                    }
                }
            }
            _ => {
                // Scalar arm: single selector.
                let sel = ctor.selector(0);
                let field = tm.mk_term(Kind::ApplySelector, &[sel.term(), t.clone()]);
                match membership_constraint(tm, field, arm_expr, name_defs, distinct_preds) {
                    Membership::Constrained(c) => conjuncts.push(c),
                    Membership::Unconstrained => {}
                    Membership::Unsupported => return Membership::Unsupported,
                }
            }
        }

        let conj = if conjuncts.len() == 1 {
            conjuncts.remove(0)
        } else {
            tm.mk_term(Kind::And, &conjuncts)
        };
        disjuncts.push(conj);
    }

    if disjuncts.is_empty() {
        return Membership::Constrained(tm.mk_boolean(false));
    }
    let term = if disjuncts.len() == 1 {
        disjuncts.remove(0)
    } else {
        tm.mk_term(Kind::Or, &disjuncts)
    };
    Membership::Constrained(term)
}

/// Recursively build a membership predicate for structured set expressions.
///
/// Handles named built-in sets, user-defined alias sets (expanded inline),
/// set literals `{n, …}`, set difference `A - B`, union `A | B`, and
/// intersection `A & B`.  Distinct user-defined sets use their uninterpreted
/// predicate from `distinct_preds`.
pub(crate) fn membership_constraint<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set_expr: &Expr,
    name_defs: &NameDefs<'_>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Membership<'tm> {
    // Fast path: datatype-sorted terms (cross-kind union values) use
    // ApplyTester / ApplySelector rather than arithmetic comparisons.
    // Tuple sorts in CVC5 are a special case of datatypes but are handled
    // by the existing `BinOp::Mul` arm below via `child()` extraction.
    if t.sort().is_dt() && !t.sort().is_tuple() {
        return membership_constraint_for_dt(tm, t, set_expr, name_defs, distinct_preds);
    }
    match &set_expr.kind {
        ExprKind::Var(sym) => match sym.0.as_str() {
            // Integer sort is the only sort in Int.  A term of distinct sort,
            // boolean sort, or tuple sort is NOT in Int.
            "Int"        => {
                if t.sort().is_integer() {
                    Membership::Unconstrained
                } else {
                    // Bool-sort, distinct-sort, tuple-sort — not in Int.
                    Membership::Constrained(tm.mk_boolean(false))
                }
            }
            // Fail is the failure singleton.  In the solver's integer model it is
            // encoded as i64::MIN so that `Nat | Fail` correctly accepts the
            // fail sentinel while rejecting all integers below zero.
            "Fail"       => {
                let Some(t) = to_integer_term(tm, t) else {
                    return Membership::Constrained(tm.mk_boolean(false));
                };
                let sentinel = tm.mk_integer(i64::MIN);
                Membership::Constrained(tm.mk_term(Kind::Equal, &[t, sentinel]))
            }
            // Bool = {0, 1} (false = 0, true = 1).
            // • boolean-sort terms are trivially in Bool — no constraint needed.
            // • integer-sort terms (e.g. from a Bool|Nat domain) need t = 0 OR t = 1.
            // Checking the term's sort avoids creating arithmetic constraints on
            // boolean-sort terms, which would cause a fatal CVC5 sort error.
            "Bool"       => {
                if t.sort().is_boolean() {
                    Membership::Unconstrained
                } else {
                    // Use to_integer_term so that tuple-sort terms correctly
                    // resolve to Constrained(false) — a tuple is never in Bool.
                    match to_integer_term(tm, t) {
                        None => Membership::Constrained(tm.mk_boolean(false)),
                        Some(t_int) => {
                            let eq0 = tm.mk_term(Kind::Equal, &[t_int.clone(), tm.mk_integer(0)]);
                            let eq1 = tm.mk_term(Kind::Equal, &[t_int, tm.mk_integer(1)]);
                            Membership::Constrained(tm.mk_term(Kind::Or, &[eq0, eq1]))
                        }
                    }
                }
            }
            "Nat"        => {
                let Some(t) = to_integer_term(tm, t) else {
                    return Membership::Constrained(tm.mk_boolean(false));
                };
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Geq, &[t, zero]))
            }
            "NatPos"     => {
                let Some(t) = to_integer_term(tm, t) else {
                    return Membership::Constrained(tm.mk_boolean(false));
                };
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Gt, &[t, zero]))
            }
            "NonZeroInt" => {
                let Some(t) = to_integer_term(tm, t) else {
                    return Membership::Constrained(tm.mk_boolean(false));
                };
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Distinct, &[t, zero]))
            }
            "Int8"   => bounded(tm, t, i8::MIN  as i64, i8::MAX  as i64),
            "Int16"  => bounded(tm, t, i16::MIN as i64, i16::MAX as i64),
            "Int32"  => bounded(tm, t, i32::MIN as i64, i32::MAX as i64),
            "Int64"  => bounded(tm, t, i64::MIN,        i64::MAX        ),
            _ => {
                // Check user-defined set definitions.
                if let Some(def) = name_defs.get(sym) {
                    match def.kind {
                        // Alias: transparent — expand to the RHS set expression.
                        DefKind::Alias => membership_constraint(tm, t, &def.value, name_defs, distinct_preds),
                        // Distinct: compare the term's CVC5 sort against the set's
                        // uninterpreted sort.  A value of the right sort is trivially
                        // a member; any other sort (integer, bool, another distinct
                        // sort, …) is definitely not a member.
                        DefKind::Distinct => {
                            if let Some(info) = distinct_preds.get(sym) {
                                if t.sort() == info.sort {
                                    Membership::Unconstrained // right sort → trivially in the set
                                } else {
                                    Membership::Constrained(tm.mk_boolean(false)) // wrong sort → never in the set
                                }
                            } else {
                                Membership::Unsupported
                            }
                        }
                    }
                } else {
                    Membership::Unsupported
                }
            }
        },

        ExprKind::SetLit(elements) => {
            if elements.is_empty() {
                return Membership::Unsupported; // empty set — caller gets Unknown
            }
            // t ∈ {v₁, v₂, …}  ↔  t == v₁  ∨  t == v₂  ∨  …
            // Constant-fold integer expressions (including negation like `-1`).
            let Some(t_int) = to_integer_term(tm, t) else {
                return Membership::Constrained(tm.mk_boolean(false));
            };
            let eqs: Option<Vec<Term<'_>>> = elements
                .iter()
                .map(|e| eval_const_int(e).map(|n| {
                    let n_term = tm.mk_integer(n);
                    tm.mk_term(Kind::Equal, &[t_int.clone(), n_term])
                }))
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
            let not_in_b = match membership_constraint(tm, t.clone(), rhs, name_defs, distinct_preds) {
                Membership::Unsupported => return Membership::Unsupported,
                Membership::Unconstrained => {
                    // B is ℤ, so A - B = ∅; nothing is a member.
                    return Membership::Unsupported;
                }
                Membership::Constrained(c) => tm.mk_term(Kind::Not, &[c]),
            };
            match membership_constraint(tm, t, lhs, name_defs, distinct_preds) {
                Membership::Unsupported => Membership::Unsupported,
                Membership::Unconstrained => Membership::Constrained(not_in_b),
                Membership::Constrained(c) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[c, not_in_b]))
                }
            }
        }

        // `Fail * B` — desugared from `!! B`.
        //
        // In the solver's integer model, `fail n` is encoded as i64::MIN + n + 1,
        // so t ∈ Fail * B  ↔  (t − (i64::MIN + 1)) ∈ B.
        // Bare `fail` (i64::MIN) is NOT in `Fail * B`; it belongs to bare `Fail`.
        //
        // We fall back to Unconstrained when B is unsupported so that an opaque
        // error set never causes a valid `!!` range to be rejected.
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs }
            if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail") =>
        {
            let Some(t) = to_integer_term(tm, t) else {
                return Membership::Constrained(tm.mk_boolean(false));
            };
            let sentinel_base = tm.mk_integer(i64::MIN.wrapping_add(1));
            let decoded = tm.mk_term(Kind::Sub, &[t, sentinel_base]);
            match membership_constraint(tm, decoded, rhs, name_defs, distinct_preds) {
                Membership::Unsupported => Membership::Unconstrained,
                other => other,
            }
        }

        // `|` in signature position means set union.
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            // t ∈ A | B  ↔  (t ∈ A) ∨ (t ∈ B)
            // Short-circuit: evaluate lhs first; if already Unconstrained the union
            // is trivially Unconstrained and we avoid constructing the rhs term
            // (which could trigger a CVC5 sort error, e.g. `bool_term >= 0` when
            // the lhs is Bool and t has boolean sort).
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            if matches!(in_a, Membership::Unconstrained) {
                return Membership::Unconstrained;
            }
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
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
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Membership::Unsupported,
                (Membership::Unconstrained, other) => other,
                (other, Membership::Unconstrained) => other,
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[a, b]))
                }
            }
        }

        // `+` in set position means disjoint union.  Membership is identical to plain
        // union — the disjointness constraint is verified separately at signature
        // check time via `validate_disjoint_unions`.
        ExprKind::BinOp { op: BinOp::Add, lhs, rhs } => {
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            if matches!(in_a, Membership::Unconstrained) {
                return Membership::Unconstrained;
            }
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Membership::Unsupported,
                (Membership::Unconstrained, _) | (_, Membership::Unconstrained) => Membership::Unconstrained,
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::Or, &[a, b]))
                }
            }
        }

        // `^` means set symmetric difference: t ∈ A ^ B ↔ (t ∈ A) XOR (t ∈ B).
        ExprKind::BinOp { op: BinOp::SymDiff, lhs, rhs } => {
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Membership::Unsupported,
                // ℤ ^ ℤ = ∅: every element is in both, so none is in exactly one.
                (Membership::Unconstrained, Membership::Unconstrained) => {
                    Membership::Constrained(tm.mk_boolean(false))
                }
                // ℤ ^ B = ℤ − B (complement of B in ℤ).
                (Membership::Unconstrained, Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::Not, &[b]))
                }
                // A ^ ℤ = ℤ − A.
                (Membership::Constrained(a), Membership::Unconstrained) => {
                    Membership::Constrained(tm.mk_term(Kind::Not, &[a]))
                }
                // (a ∨ b) ∧ ¬(a ∧ b)
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    let or_ab  = tm.mk_term(Kind::Or,  &[a.clone(), b.clone()]);
                    let and_ab = tm.mk_term(Kind::And, &[a, b]);
                    let xor    = tm.mk_term(Kind::And, &[or_ab, tm.mk_term(Kind::Not, &[and_ab])]);
                    Membership::Constrained(xor)
                }
            }
        }

        ExprKind::Comprehension { output, var, source, filter } => {
            comprehension_membership(tm, t, output, var, source, filter.as_deref(), name_defs, distinct_preds)
        }

        // `t ∈ X*`  ↔  every element of `t` is in `X`.
        //
        // Two representations of `t`:
        //
        // (a) Sequence-sorted term (variable-length parameter encoded as `(Seq elem)`):
        //     Encode as a universally-quantified constraint:
        //       ∀ i. 0 ≤ i < len(t)  →  nth(t, i) ∈ X
        //     If the element membership is Unconstrained (e.g. X = Int), the entire
        //     sequence is trivially unconstrained.  If element membership is Unsupported,
        //     propagate Unsupported (→ Unknown at the call site).
        //
        // (b) Tuple-sorted term (fixed-length concrete bodies like `[1, 2, 3]`):
        //     Read the element count from the tuple sort and check each child against X.
        //     An empty tuple `[]` satisfies any `X*` vacuously.
        ExprKind::KleeneStar(inner) => {
            if t.sort().is_sequence() {
                // Build a bound variable `i` for the universal quantifier.
                let i = tm.mk_var(tm.integer_sort(), "i");
                // nth(t, i) — the i-th element of the sequence.
                let nth = tm.mk_term(Kind::SeqNth, &[t.clone(), i.clone()]);
                return match membership_constraint(tm, nth, inner, name_defs, distinct_preds) {
                    Membership::Unconstrained => Membership::Unconstrained,
                    Membership::Unsupported   => Membership::Unsupported,
                    Membership::Constrained(elem_c) => {
                        let len   = tm.mk_term(Kind::SeqLength, &[t]);
                        let lo    = tm.mk_term(Kind::Leq, &[tm.mk_integer(0), i.clone()]);
                        let hi    = tm.mk_term(Kind::Lt,  &[i.clone(), len]);
                        let guard = tm.mk_term(Kind::And, &[lo, hi]);
                        let body  = tm.mk_term(Kind::Implies, &[guard, elem_c]);
                        let vars  = tm.mk_term(Kind::VariableList, &[i]);
                        Membership::Constrained(tm.mk_term(Kind::Forall, &[vars, body]))
                    }
                };
            }
            if !t.sort().is_tuple() {
                return Membership::Unsupported;
            }
            // Tuple branch: fixed-length concrete body.
            let dt = t.sort().datatype();
            let n_elems = dt.constructor(0).num_selectors();
            let mut constraints: Vec<Term<'_>> = Vec::new();
            for i in 0..n_elems {
                let elem = t.child(i + 1);
                match membership_constraint(tm, elem, inner, name_defs, distinct_preds) {
                    Membership::Constrained(c) => constraints.push(c),
                    Membership::Unconstrained => {}
                    Membership::Unsupported => return Membership::Unsupported,
                }
            }
            match constraints.len() {
                0 => Membership::Unconstrained,
                1 => Membership::Constrained(constraints.remove(0)),
                _ => Membership::Constrained(tm.mk_term(Kind::And, &constraints)),
            }
        }

        // `t ∈ A * B`  ↔  `proj0(t) ∈ A ∧ proj1(t) ∈ B`
        // `t` is always a mk_tuple(…) term; use child(i+1) to extract
        // element i (child 0 is the APPLY_CONSTRUCTOR constructor).
        // A non-tuple term (integer, boolean) can never be a product-set member.
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            if !t.sort().is_tuple() {
                return Membership::Constrained(tm.mk_boolean(false));
            }
            use super::sort::flatten_product;
            let parts = flatten_product(set_expr);
            let mut constraints: Vec<Term<'_>> = Vec::new();
            for (i, part) in parts.iter().enumerate() {
                let proj = t.child(i + 1);
                match membership_constraint(tm, proj, part, name_defs, distinct_preds) {
                    Membership::Unsupported => return Membership::Unsupported,
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => constraints.push(c),
                }
            }
            match constraints.len() {
                0 => Membership::Unconstrained,
                1 => Membership::Constrained(constraints.remove(0)),
                _ => Membership::Constrained(tm.mk_term(Kind::And, &constraints)),
            }
        }

        _ => Membership::Unsupported,
    }
}

/// Encode `t ∈ { output for var in source if filter }` as a cvc5 predicate.
///
/// Two strategies:
/// - Finite literal source: unroll into a disjunction of equalities (one per element).
/// - Identity output (`{x for x in S if P(x)}`): encode as `t ∈ S ∧ P(t)`.
/// - All other cases: `Unsupported` (Unknown at the solver level).
fn comprehension_membership<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    output: &Expr,
    var: &Symbol,
    source: &Expr,
    filter: Option<&Expr>,
    name_defs: &NameDefs<'_>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Membership<'tm> {
    // Case 1: source is a finite set literal — unroll.
    if let ExprKind::SetLit(elements) = &source.kind {
        if elements.is_empty() {
            return Membership::Constrained(tm.mk_boolean(false));
        }
        let mut disjuncts: Vec<Term<'_>> = Vec::new();
        for elem in elements {
            let ExprKind::IntLit(n) = &elem.kind else { return Membership::Unsupported; };
            let elem_term = tm.mk_integer(*n);
            let Some(out_term) = encode_comp_expr(output, var, elem_term.clone(), tm, name_defs, distinct_preds) else {
                return Membership::Unsupported;
            };
            let eq = tm.mk_term(Kind::Equal, &[t.clone(), out_term]);
            if let Some(f) = filter {
                let Some(filter_term) = encode_comp_expr(f, var, elem_term, tm, name_defs, distinct_preds) else {
                    return Membership::Unsupported;
                };
                disjuncts.push(tm.mk_term(Kind::And, &[filter_term, eq]));
            } else {
                disjuncts.push(eq);
            }
        }
        let combined = if disjuncts.len() == 1 {
            disjuncts.remove(0)
        } else {
            tm.mk_term(Kind::Or, &disjuncts)
        };
        return Membership::Constrained(combined);
    }

    // Case 2: output is the identity (just the bound variable).
    // t ∈ {x for x in S if P(x)}  →  t ∈ S  ∧  P(t)
    if let ExprKind::Var(sym) = &output.kind {
        if sym == var {
            let source_mem = membership_constraint(tm, t.clone(), source, name_defs, distinct_preds);
            let filter_mem = match filter {
                None => None,
                Some(f) => match encode_comp_expr(f, var, t.clone(), tm, name_defs, distinct_preds) {
                    Some(term) => Some(term),
                    None => return Membership::Unsupported,
                },
            };
            return match (source_mem, filter_mem) {
                (Membership::Unsupported, _) => Membership::Unsupported,
                (mem, None) => mem,
                (Membership::Unconstrained, Some(f)) => Membership::Constrained(f),
                (Membership::Constrained(s), Some(f)) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[s, f]))
                }
            };
        }
    }

    Membership::Unsupported
}

/// Encode a Cantor expression as a cvc5 term, substituting `var_term` for the
/// bound variable `var`.  Only handles arithmetic and comparisons — enough for
/// comprehension output expressions and filter predicates.  Returns `None` for
/// anything more complex (calls, if-then-else, etc.).
fn encode_comp_expr<'tm>(
    expr: &Expr,
    var: &Symbol,
    var_term: Term<'tm>,
    tm: &'tm TermManager,
    name_defs: &NameDefs<'_>,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<Term<'tm>> {
    match &expr.kind {
        ExprKind::IntLit(n)  => Some(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Some(tm.mk_boolean(*b)),
        ExprKind::Var(sym) if sym == var => Some(var_term),
        ExprKind::Var(_) => None, // free variable — not the bound var; unsupported
        ExprKind::UnOp { op, expr: inner } => {
            let t = encode_comp_expr(inner, var, var_term, tm, name_defs, distinct_preds)?;
            match op {
                UnOp::Neg => Some(tm.mk_term(Kind::Neg, &[t])),
                UnOp::Not => Some(tm.mk_term(Kind::Not, &[t])),
            }
        }
        ExprKind::BinOp { op, lhs, rhs } => {
            match op {
                BinOp::In | BinOp::NotIn => {
                    let l = encode_comp_expr(lhs, var, var_term.clone(), tm, name_defs, distinct_preds)?;
                    let mem = membership_constraint(tm, l, rhs, name_defs, distinct_preds);
                    return match (op, mem) {
                        (BinOp::In,    Membership::Constrained(c))  => Some(c),
                        (BinOp::In,    Membership::Unconstrained)    => Some(tm.mk_boolean(true)),
                        (BinOp::NotIn, Membership::Constrained(c))  => Some(tm.mk_term(Kind::Not, &[c])),
                        (BinOp::NotIn, Membership::Unconstrained)    => Some(tm.mk_boolean(false)),
                        _ => None,
                    };
                }
                _ => {}
            }
            let l = encode_comp_expr(lhs, var, var_term.clone(), tm, name_defs, distinct_preds)?;
            let r = encode_comp_expr(rhs, var, var_term, tm, name_defs, distinct_preds)?;
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
                BinOp::Union | BinOp::Intersect | BinOp::SymDiff => return None,
            };
            Some(tm.mk_term(kind, &[l, r]))
        }
        _ => None, // Call, If, Try, SetLit, Comprehension — unsupported
    }
}

pub(crate) fn bounded<'tm>(tm: &'tm TermManager, t: Term<'tm>, min: i64, max: i64) -> Membership<'tm> {
    let Some(t) = to_integer_term(tm, t) else {
        return Membership::Constrained(tm.mk_boolean(false));
    };
    let lo  = tm.mk_integer(min);
    let hi  = tm.mk_integer(max);
    let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
    let leq = tm.mk_term(Kind::Leq, &[t, hi]);
    Membership::Constrained(tm.mk_term(Kind::And, &[geq, leq]))
}
