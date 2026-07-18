//! `membership_constraint`'s two structural pre-checks: cross-kind union
//! datatype membership, and sequence-unification (a sequence-sorted term
//! checked against an atomic scalar/product set).
//!
//! Split out of `membership.rs` as a pure refactor (no behaviour change) to
//! keep that file under the repo's line-count guideline — mirrors phase 1's
//! own `encode.rs` → `encode_call.rs` split.

use cvc5::{Kind, Term, TermManager};

use crate::ast::BinOp;
use crate::semantics::builtins;
use crate::semantics::tree::{SemExpr, SemExprKind, flatten_any_union, flatten_cartesian_product};

use super::NameDefs;
use super::membership::{Membership, SolverPreds, eval_const_int, membership_constraint};

/// Membership predicate for a term whose CVC5 sort is an algebraic datatype.
///
/// Handles cross-kind union values: `t ∈ set_expr` where `t` has a DT sort
/// built by `build_union_datatype_sort` (each arm has ONE selector whose sort
/// is the arm's natural CVC5 sort).  For each arm we emit:
///   `is_Arm(t)  ∧  membership_constraint(selector(0)(t), arm_expr)`
/// This is fully recursive and sort-agnostic: tuple, sequence, scalar, and
/// distinct-sort arms are all handled uniformly.
pub(super) fn membership_constraint_for_dt<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set_expr: &SemExpr,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Membership<'tm> {
    let dt = t.sort().datatype();
    // `^` (SymDiff) builds its cross-kind DT with exactly `[lhs, rhs]` as the two
    // constructor arms (see `set_sort`) rather than going through the recursive
    // Union/DisjointUnion flattening — the two sides are provably disjoint in
    // exactly the situations where a DT is built for `^`, so OR-of-arms (what
    // this function computes) already equals the true XOR.
    let arm_exprs: Vec<&SemExpr> = match &set_expr.kind {
        SemExprKind::BinOp {
            op: BinOp::SymDiff,
            lhs,
            rhs,
        } => vec![lhs.as_ref(), rhs.as_ref()],
        _ => flatten_any_union(set_expr),
    };

    let mut disjuncts: Vec<Term<'_>> = Vec::new();
    // Match by *position*, not by constructor name: `dt` was built by
    // `build_union_datatype_sort` iterating this exact `arm_exprs` list (see
    // `set_sort`'s cross-kind Union arm, which flattens the same `set_expr`
    // via the same `flatten_any_union`/`[lhs, rhs]` split before calling it)
    // in the same order, so `dt.constructor(i)` always corresponds to
    // `arm_exprs[i]` — no name lookup needed. This also sidesteps a latent
    // name-collision hazard the old `find(|c| c.name() == ctor_name)` had:
    // `arm_ctor_name`/`arm_ctor_name_for_arm` derive a constructor's name
    // purely from its Kind, so two arms sharing a Kind (allowed for named-
    // union labeled arms, e.g. `Circle: Nat | Square: NatPos`) get the same
    // declared name, and `find` would silently resolve both to whichever
    // constructor happens to come first.
    for (i, arm_expr) in arm_exprs.into_iter().enumerate() {
        if i >= dt.num_constructors() {
            continue;
        }
        let ctor = dt.constructor(i);

        let tester = tm.mk_term(Kind::ApplyTester, &[ctor.tester_term(), t.clone()]);
        let mut conjuncts: Vec<Term<'_>> = vec![tester];

        // Each constructor has exactly one selector `f0` holding the arm's
        // natural-sort value.  Recursively check membership in the arm's set.
        let sel = ctor.selector(0);
        let field = tm.mk_term(Kind::ApplySelector, &[sel.term(), t.clone()]);
        match membership_constraint(tm, field, arm_expr, name_defs, distinct_preds) {
            Membership::Constrained(c) => conjuncts.push(c),
            Membership::Unconstrained => {}
            Membership::Unsupported => return Membership::Unsupported,
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

// ── Sequence-unification helpers ─────────────────────────────────────────────

/// Returns true for set expressions that represent "atomic" (scalar or fixed-length)
/// sets — i.e. sets whose elements have a concrete, finite length when viewed as
/// sequences.  Used to decide when a sequence-sorted term should be lifted by length.
///
/// Built-in scalar named sets, set literals, and Cartesian products are atomic.
/// Kleene-star sets, unions, comprehensions, and user-defined distinct sets
/// are NOT atomic (they contain elements of varying length or unknown structure).
/// User-defined aliases fall through to their own `Var` arm, which recurses
/// into the alias body — they may end up atomic or not depending on that body.
pub(super) fn is_atomic_set(set_expr: &SemExpr) -> bool {
    match &set_expr.kind {
        SemExprKind::Var(sym) => builtins::lookup(&sym.0).is_some(),
        SemExprKind::SetLit(_) => true,
        SemExprKind::CartesianProduct(..) => true,
        _ => false,
    }
}

/// Encode `t ∈ set_expr` for a *sequence-sorted* term `t` against an *atomic* set.
///
/// Under the sequence-unification model `n ∈ Nat*` and `(a,b) ∈ Nat*` both hold
/// because scalars and tuples are identified with fixed-length sequences.  The
/// reverse direction handled here: `t ∈ Nat` (for sequence-sorted `t`) is true iff
/// `len(t) == 1  ∧  nth(t,0) ∈ Nat`.  Products check the appropriate N-ary length.
/// Set literals handle `[]` (empty-sequence element, encoding `len(t) == 0`) and
/// integer elements (encoding `len(t) == 1 ∧ nth(t,0) == n`).
pub(super) fn lift_sequence_into_atomic<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set_expr: &SemExpr,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Membership<'tm> {
    match &set_expr.kind {
        // Product A*B*C: t ∈ A*B*C ⟺ len(t)==N ∧ nth(t,0)∈A ∧ nth(t,1)∈B ∧ …
        SemExprKind::CartesianProduct(..) => {
            let parts = flatten_cartesian_product(set_expr);
            let n = parts.len() as i64;
            let len_term = tm.mk_term(Kind::SeqLength, std::slice::from_ref(&t));
            let len_eq = tm.mk_term(Kind::Equal, &[len_term, tm.mk_integer(n)]);
            let mut constraints = vec![len_eq];
            for (j, part) in parts.iter().enumerate() {
                let nth = tm.mk_term(Kind::SeqNth, &[t.clone(), tm.mk_integer(j as i64)]);
                match membership_constraint(tm, nth, part, name_defs, distinct_preds) {
                    Membership::Constrained(c) => constraints.push(c),
                    Membership::Unconstrained => {}
                    Membership::Unsupported => return Membership::Unsupported,
                }
            }
            Membership::Constrained(if constraints.len() == 1 {
                constraints.remove(0)
            } else {
                tm.mk_term(Kind::And, &constraints)
            })
        }

        // SetLit: handle the empty-sequence element `[]` (Tuple([])) and integer
        // constants.  Non-empty-tuple elements (like `[1,2]`) are deferred.
        // TODO: support general sequence-literal set elements like `{[1,2], [3]}`
        SemExprKind::SetLit(elements) => {
            if elements.is_empty() {
                return Membership::Constrained(tm.mk_boolean(false));
            }
            let len_term = tm.mk_term(Kind::SeqLength, std::slice::from_ref(&t));
            let mut disjuncts: Vec<Term<'_>> = Vec::new();
            for elem in elements {
                match &elem.kind {
                    // `[]` — the empty sequence; t ∈ {[]} ⟺ len(t) == 0
                    SemExprKind::Tuple(parts) if parts.is_empty() => {
                        disjuncts
                            .push(tm.mk_term(Kind::Equal, &[len_term.clone(), tm.mk_integer(0)]));
                    }
                    // integer-valued element: t ∈ {n} ⟺ len(t)==1 ∧ nth(t,0)==n
                    _ => match eval_const_int(elem) {
                        Some(n) => {
                            let nth0 = tm.mk_term(Kind::SeqNth, &[t.clone(), tm.mk_integer(0)]);
                            let len1 =
                                tm.mk_term(Kind::Equal, &[len_term.clone(), tm.mk_integer(1)]);
                            let eq_n = tm.mk_term(Kind::Equal, &[nth0, tm.mk_integer(n)]);
                            disjuncts.push(tm.mk_term(Kind::And, &[len1, eq_n]));
                        }
                        None => return Membership::Unsupported,
                    },
                }
            }
            Membership::Constrained(if disjuncts.len() == 1 {
                disjuncts.remove(0)
            } else {
                tm.mk_term(Kind::Or, &disjuncts)
            })
        }

        // Scalar named set (Int, Nat, NatPos, etc.): t ∈ S ⟺ len(t)==1 ∧ nth(t,0) ∈ S
        // The recursive call will use the normal scalar path (nth0 has integer sort).
        _ => {
            let len_term = tm.mk_term(Kind::SeqLength, std::slice::from_ref(&t));
            let len1 = tm.mk_term(Kind::Equal, &[len_term, tm.mk_integer(1)]);
            let nth0 = tm.mk_term(Kind::SeqNth, &[t, tm.mk_integer(0)]);
            match membership_constraint(tm, nth0, set_expr, name_defs, distinct_preds) {
                Membership::Unconstrained => Membership::Constrained(len1),
                Membership::Constrained(elem_c) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[len1, elem_c]))
                }
                Membership::Unsupported => Membership::Unsupported,
            }
        }
    }
}
