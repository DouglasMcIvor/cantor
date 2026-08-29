//! Set membership encoding — mapping Cantor set expressions to cvc5 predicates.

use std::collections::HashMap;

use cvc5::{Kind, Sort, Term, TermManager};

use crate::ast::{BinOp, UnOp};
use crate::semantics::tree::{SemExpr, SemExprKind, flatten_cartesian_product};
use crate::span::Symbol;

use super::NameDefs;
use super::membership_comp::{CompCtx, comprehension_membership, encode_comp_expr};
use super::membership_named::membership_constraint_for_named;
use super::membership_seq::{
    is_atomic_set, lift_sequence_into_atomic, membership_constraint_for_dt,
};

/// Per-distinct-set CVC5 artefacts created when `D = distinct B` is declared.
///
/// Each distinct set gets its own opaque CVC5 uninterpreted sort so the solver
/// cannot confuse values of different distinct sets or of their basis.
#[derive(Clone)]
pub(crate) struct DistinctInfo<'tm> {
    /// Opaque CVC5 sort — every D-value has this sort.
    pub(crate) sort: Sort<'tm>,
    /// Constructor UF: `mk_D : basis_sort → D_sort`, where `basis_sort` is
    /// `B`'s own CVC5 sort (`solver::preds::build_distinct_preds`) — `Int`
    /// for `Litre = distinct Nat`, but not always (see that function's doc
    /// comment). Applying `mk_D(b)` wraps a `B`-sorted value as a D-value.
    pub(crate) mk: Term<'tm>,
    /// Destructor UF: `from_D : D_sort → basis_sort`.
    /// Applying `from_D(x)` extracts the underlying `B`-sorted value from a
    /// D-value.
    pub(crate) from: Term<'tm>,
}

/// Map from distinct set name to its CVC5 encoding artefacts.
pub(crate) type DistinctPreds<'tm> = HashMap<Symbol, DistinctInfo<'tm>>;

/// Per-wrapping-sort CVC5 artefacts for `Signed32`/`Unsigned32`
/// (docs/wrapping-and-quotient-sets-plan.md, Feature 1).
///
/// Structurally like `DistinctInfo` (own opaque sort + constructor/destructor
/// uninterpreted functions), but `mk`/`from` connect straight to a native
/// `(_ BitVec width)` term, not `Int` — every `+ - * neg`/comparison between
/// two same-family operands stays entirely in bit-vector land (`bvadd` etc.
/// on `from_D(x)`/`from_D(y)`, then `mk_D(...)`), so `Int ↔ BitVec`
/// conversion only happens at the two genuine boundary points: the
/// user-facing constructor (`signed32(n)`, `int2bv`) and `from(x)` (`ubv_to_int`/
/// `sbv_to_int`, depending on `signed`).
#[derive(Clone)]
pub(crate) struct WrappingInfo<'tm> {
    pub(crate) width: u32,
    pub(crate) signed: bool,
    /// Opaque CVC5 sort — every value of this wrapping set has this sort.
    pub(crate) d_sort: Sort<'tm>,
    /// Constructor UF: `mk_D : BitVec(width) → D_sort`.
    pub(crate) mk: Term<'tm>,
    /// Destructor UF: `from_D : D_sort → BitVec(width)`.
    pub(crate) from: Term<'tm>,
}

/// Map from wrapping-set builtin name (`"Signed32"`/`"Unsigned32"`) to its
/// CVC5 encoding artefacts.
pub(crate) type WrappingPreds<'tm> = HashMap<Symbol, WrappingInfo<'tm>>;

/// Per-quotient-set artefacts created for `L / canon` (see
/// `build_quotient_preds`). Keyed by the canonicalizer's own `Symbol` (not
/// the quotient set's name, if any — the same canonicalizer reference is
/// valid whether or not it's bound to a name), since that's exactly what a
/// `SemExprKind::SetQuotient` node carries.
///
/// Deliberately holds the canonicalizer's raw ingredients (param + body),
/// not a precomputed CVC5 uninterpreted-function-plus-defining-axiom: an
/// earlier version built `canon : sort -> sort` once per solver instance
/// and asserted `∀x. canon(x) == body(x)` unconditionally — which injects a
/// quantified fact into *every* per-signature proof in the file, including
/// ones with nothing to do with this quotient set, and was observed to make
/// cvc5 hang (the same quantifier/nonlinear-interaction risk this codebase
/// already works around elsewhere, e.g. the nl-cov note). Encoding the body
/// on demand via `encode_comp_expr` — substituting the *specific* term
/// being checked, no quantifier involved — avoids that entirely; only the
/// one-time idempotence proof (`check_quotient_def`, run once per quotient
/// definition, in its own isolated solver) still needs a quantifier.
#[derive(Clone)]
pub(crate) struct QuotientInfo<'tm> {
    /// `L`'s own sort — quotient values are represented identically to
    /// their canonical representative, no wrapper sort. Used only to
    /// fast-reject a wrong-sort term before attempting to encode anything.
    pub(crate) sort: Sort<'tm>,
    /// The canonicalizer's own parameter name — substituted for by
    /// `encode_comp_expr` when evaluating `body` at a concrete term.
    pub(crate) param: Symbol,
    /// The canonicalizer's body (already validated elsewhere to be a
    /// single expression, not a block — see `resolve_canonicalizer`).
    pub(crate) body: SemExpr,
}

/// Map from canonicalizer symbol to its CVC5 encoding artefacts.
pub(crate) type QuotientPreds<'tm> = HashMap<Symbol, QuotientInfo<'tm>>;

/// Bundles all three cross-cutting "opaque identity" registries
/// `membership_constraint` needs. Kept as one struct — threaded through the
/// same parameter/field every `distinct_preds` caller already passes today
/// — rather than adding new parameters everywhere: `Deref` to the inner
/// `DistinctPreds` means the ~40 call sites that only ever read distinct-set
/// info need no changes, since `&SolverPreds` coerces to `&DistinctPreds`
/// automatically wherever that's still what's expected. Only construction
/// sites and the handful of call sites that need `.wrapping`/`.quotient`
/// directly (a small superset of `set_sort`'s own callers, since a wrapping
/// value's sort is now also decided there) need updating.
pub(crate) struct SolverPreds<'tm> {
    pub(crate) distinct: DistinctPreds<'tm>,
    pub(crate) wrapping: WrappingPreds<'tm>,
    pub(crate) quotient: QuotientPreds<'tm>,
}

impl<'tm> std::ops::Deref for SolverPreds<'tm> {
    type Target = DistinctPreds<'tm>;
    fn deref(&self) -> &DistinctPreds<'tm> {
        &self.distinct
    }
}

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
pub(super) fn eval_const_int(expr: &SemExpr) -> Option<i64> {
    match &expr.kind {
        SemExprKind::IntLit(n) => Some(*n),
        SemExprKind::UnOp {
            op: UnOp::Neg,
            expr: inner,
        } => eval_const_int(inner).map(|n| -n),
        _ => None,
    }
}

/// Build the predicate `t == elem` for one literal `SetLit` element, so its
/// membership arm can compare `t` against each element at the element's own
/// natural sort instead of assuming integer. Returns `None` for anything
/// that isn't one of these literal shapes — the caller reports `Unsupported`
/// rather than silently treating an un-encodable element as "never a member"
/// (which would be unsound wherever the resulting `Membership::Constrained`
/// is asserted as a domain hypothesis — see `build_param_terms`). A literal
/// whose *natural* sort doesn't match `t`'s own sort can never equal `t` —
/// that's `Some(false)`, not `None` (`None` means "don't know how to
/// encode this element at all", not "definitely not equal").
fn literal_element_predicate<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    e: &SemExpr,
    distinct_preds: &SolverPreds<'tm>,
) -> Option<Term<'tm>> {
    if let Some(n) = eval_const_int(e) {
        return Some(if t.sort().is_integer() {
            tm.mk_term(Kind::Equal, &[t, tm.mk_integer(n)])
        } else {
            tm.mk_boolean(false)
        });
    }
    Some(match &e.kind {
        SemExprKind::BoolLit(b) => {
            if t.sort().is_boolean() {
                tm.mk_term(Kind::Equal, &[t, tm.mk_boolean(*b)])
            } else {
                tm.mk_boolean(false)
            }
        }
        // `'c'` — compare via `from_Char(t) == n`, *not* `t == mk_Char(n)`.
        // This function has no `&mut Solver` to assert onto, so it can't
        // give this specific literal its own `from(mk_Char(n)) == n`
        // round-trip fact (see `solver::encode`'s `CharLit` arm, which does
        // have solver access and asserts exactly that whenever a literal is
        // encoded in value position). Without that fact, `t == mk_Char(n)`
        // would be sound but incomplete: cvc5 has no reason to know
        // `mk_Char(97) != mk_Char(98)` unless *both* literals' round-trips
        // happen to already be asserted elsewhere in the same proof — e.g.
        // `t' == mk_Char(97)` could be found consistent with a model where
        // `mk_Char(97) == mk_Char(98)`, spuriously refuting `t ∈ Char -
        // {'a'}` for `t = mk_Char(98)`. `from` is already the correct,
        // deterministic inverse for any legitimately-constructed Char value
        // (every construction site — `char(n)`, `'c'` in value position —
        // asserts its own round-trip), so comparing its *decoded* codepoint
        // needs no injectivity assumption about `mk_Char` at all.
        SemExprKind::CharLit(c) => {
            let info = distinct_preds.get(&Symbol::new("Char"))?;
            if t.sort() == info.sort {
                let from_t = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), t]);
                tm.mk_term(Kind::Equal, &[from_t, tm.mk_integer(*c as u32 as i64)])
            } else {
                tm.mk_boolean(false)
            }
        }
        _ => return None,
    })
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
    set_expr: &SemExpr,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Membership<'tm> {
    // Fast path: datatype-sorted terms (cross-kind union values) use
    // ApplyTester / ApplySelector rather than arithmetic comparisons.
    // Tuple sorts in CVC5 are a special case of datatypes but are handled
    // by the existing `CartesianProduct` arm below via `child()` extraction.
    if t.sort().is_dt() && !t.sort().is_tuple() {
        return membership_constraint_for_dt(tm, t, set_expr, name_defs, distinct_preds);
    }
    // Sequence-unification Direction 2: a sequence-sorted term checked against an
    // *atomic* set (scalar or product) is lifted by length.  Compound set operators
    // (Sub, Union, KleeneStar, …) are not intercepted here — they fall through to
    // their own arms, which recurse and re-enter this guard on atomic leaves.
    if t.sort().is_sequence() && is_atomic_set(set_expr) {
        return lift_sequence_into_atomic(tm, t, set_expr, name_defs, distinct_preds);
    }
    match &set_expr.kind {
        // Builtins (`Int`, `Bool`, `Char`, `Rational`, `Signed32`/`Unsigned32`,
        // `Fail`, `None`, …) and user `alias`/`distinct` names — see
        // `membership_named.rs`.
        SemExprKind::Var(sym) => {
            membership_constraint_for_named(tm, t, sym, name_defs, distinct_preds)
        }

        SemExprKind::SetLit(elements) => {
            if elements.is_empty() {
                // ∅ has no members: t ∈ {} is always false.
                // Returning Constrained(false) rather than Unsupported lets
                // set-difference work correctly: t ∈ (A - {}) = t ∈ A ∧ ¬false = t ∈ A.
                return Membership::Constrained(tm.mk_boolean(false));
            }
            // t ∈ {v₁, v₂, …}  ↔  t == v₁  ∨  t == v₂  ∨  …
            // Each element is encoded at its own natural sort
            // (`literal_element_predicate`) rather than assuming integer, so
            // e.g. `t ∈ {'a', 'b'}` works when `t` is Char-sorted. `[]`
            // (empty tuple = empty sequence) is never equal to a scalar, so
            // it contributes `false` to the disjunction and is simply
            // skipped. An element whose predicate can't be built at all is
            // genuinely unsupported syntax → Unsupported.
            let mut eqs: Vec<Term<'_>> = Vec::new();
            for e in elements {
                if matches!(&e.kind, SemExprKind::Tuple(parts) if parts.is_empty()) {
                    // Scalar ≠ empty sequence — skip (contributes false).
                    continue;
                }
                let Some(pred) = literal_element_predicate(tm, t.clone(), e, distinct_preds) else {
                    return Membership::Unsupported;
                };
                eqs.push(pred);
            }
            Membership::Constrained(match eqs.len() {
                0 => tm.mk_boolean(false),
                1 => eqs.remove(0),
                _ => tm.mk_term(Kind::Or, &eqs),
            })
        }

        // `-` in signature position means set difference (A ∖ B).
        SemExprKind::SetDifference(lhs, rhs) => {
            // t ∈ A - B  ↔  (t ∈ A) ∧ ¬(t ∈ B)
            let not_in_b =
                match membership_constraint(tm, t.clone(), rhs, name_defs, distinct_preds) {
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

        // `|` in signature position means set union.
        SemExprKind::BinOp {
            op: BinOp::Union,
            lhs,
            rhs,
        } => {
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
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => {
                    Membership::Unsupported
                }
                (Membership::Unconstrained, _) | (_, Membership::Unconstrained) => {
                    Membership::Unconstrained
                }
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::Or, &[a, b]))
                }
            }
        }

        // `&` in signature position means set intersection.
        SemExprKind::BinOp {
            op: BinOp::Intersect,
            lhs,
            rhs,
        } => {
            // t ∈ A & B  ↔  (t ∈ A) ∧ (t ∈ B)
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => {
                    Membership::Unsupported
                }
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
        SemExprKind::DisjointUnion(lhs, rhs) => {
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            if matches!(in_a, Membership::Unconstrained) {
                return Membership::Unconstrained;
            }
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => {
                    Membership::Unsupported
                }
                (Membership::Unconstrained, _) | (_, Membership::Unconstrained) => {
                    Membership::Unconstrained
                }
                (Membership::Constrained(a), Membership::Constrained(b)) => {
                    Membership::Constrained(tm.mk_term(Kind::Or, &[a, b]))
                }
            }
        }

        // `^` means set symmetric difference: t ∈ A ^ B ↔ (t ∈ A) XOR (t ∈ B).
        SemExprKind::BinOp {
            op: BinOp::SymDiff,
            lhs,
            rhs,
        } => {
            let in_a = membership_constraint(tm, t.clone(), lhs, name_defs, distinct_preds);
            let in_b = membership_constraint(tm, t, rhs, name_defs, distinct_preds);
            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => {
                    Membership::Unsupported
                }
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
                    let or_ab = tm.mk_term(Kind::Or, &[a.clone(), b.clone()]);
                    let and_ab = tm.mk_term(Kind::And, &[a, b]);
                    let xor = tm.mk_term(Kind::And, &[or_ab, tm.mk_term(Kind::Not, &[and_ab])]);
                    Membership::Constrained(xor)
                }
            }
        }

        SemExprKind::Comprehension {
            output,
            var,
            source,
            filter,
        } => comprehension_membership(
            t,
            output,
            var,
            source,
            filter.as_deref(),
            CompCtx {
                tm,
                name_defs,
                distinct_preds,
            },
        ),

        // `t ∈ X*`  ↔  every element of `t` is in `X`.
        //
        // Under the sequence-unification model, scalars and tuples are identified with
        // fixed-length sequences, so there are three representations of `t`:
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
        //
        // (c) Scalar term (integer- or boolean-sorted): identified with the length-1
        //     sequence `[t]`, so `t ∈ X*`  ⟺  `t ∈ X`.  This lets `foo() = 5`
        //     prove against a range of `Nat*`, and lets `bar(5)` pass a scalar to a
        //     `Nat*` parameter (the codegen boxes it at the call boundary).
        SemExprKind::KleeneStar(inner) => {
            if t.sort().is_sequence() {
                // Build a bound variable `i` for the universal quantifier.
                let i = tm.mk_var(tm.integer_sort(), "i");
                // nth(t, i) — the i-th element of the sequence.
                let nth = tm.mk_term(Kind::SeqNth, &[t.clone(), i.clone()]);
                return match membership_constraint(tm, nth, inner, name_defs, distinct_preds) {
                    Membership::Unconstrained => Membership::Unconstrained,
                    Membership::Unsupported => Membership::Unsupported,
                    Membership::Constrained(elem_c) => {
                        let len = tm.mk_term(Kind::SeqLength, &[t]);
                        let lo = tm.mk_term(Kind::Leq, &[tm.mk_integer(0), i.clone()]);
                        let hi = tm.mk_term(Kind::Lt, &[i.clone(), len]);
                        let guard = tm.mk_term(Kind::And, &[lo, hi]);
                        let body = tm.mk_term(Kind::Implies, &[guard, elem_c]);
                        let vars = tm.mk_term(Kind::VariableList, &[i]);
                        Membership::Constrained(tm.mk_term(Kind::Forall, &[vars, body]))
                    }
                };
            }
            if t.sort().is_integer() || t.sort().is_boolean() {
                // Scalar is identified with the length-1 sequence [t]: t ∈ X* ⟺ t ∈ X.
                return membership_constraint(tm, t, inner, name_defs, distinct_preds);
            }
            if !t.sort().is_tuple() {
                return Membership::Unsupported;
            }
            // Tuple branch: fixed-length concrete body.
            // Use ApplySelector rather than child(i+1) — `t` may be an opaque
            // tuple-sorted term (e.g. a SeqNth result or a local let-bound tuple
            // constant), which carries no APPLY_CONSTRUCTOR children.
            let dt = t.sort().datatype();
            let ctor = dt.constructor(0);
            let n_elems = ctor.num_selectors();
            let mut constraints: Vec<Term<'_>> = Vec::new();
            for i in 0..n_elems {
                let sel = ctor.selector(i);
                let elem = tm.mk_term(Kind::ApplySelector, &[sel.term(), t.clone()]);
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
        // Use ApplySelector rather than child(i+1) so this works for any
        // tuple-sorted term — including SeqNth results (which are NOT
        // APPLY_CONSTRUCTOR terms; child() would give the wrong children).
        // A non-tuple term (integer, boolean) can never be a product-set member.
        SemExprKind::CartesianProduct(..) => {
            if !t.sort().is_tuple() {
                return Membership::Constrained(tm.mk_boolean(false));
            }
            let parts = flatten_cartesian_product(set_expr);
            let dt = t.sort().datatype();
            let ctor = dt.constructor(0); // tuples have exactly one constructor
            let mut constraints: Vec<Term<'_>> = Vec::new();
            for (j, part) in parts.iter().enumerate() {
                let sel = ctor.selector(j);
                let proj = tm.mk_term(Kind::ApplySelector, &[sel.term(), t.clone()]);
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

        // `L / canon` — quotient set. Membership is the canonicalizer's fixed
        // points: `x ∈ L/canon ⟺ x ∈ L ∧ canon(x) == x`. `canon(t)` is
        // encoded on demand for this *specific* `t` via `encode_comp_expr`
        // (no quantifier, no persistent axiom — see `QuotientInfo`'s doc
        // comment for why). Looked up by the canonicalizer's own symbol;
        // absent, or a body `encode_comp_expr` can't handle, means either
        // the quotient definition failed validation (already reported
        // elsewhere as a compile error) or this call site never had
        // `fn_env` available to register it (e.g. an auxiliary pass like
        // `domain_within_int64`) — either way, `Unsupported` degrades to
        // `Unknown` rather than guessing.
        SemExprKind::SetQuotient(lhs, canon_sym) => {
            let Some(info) = distinct_preds.quotient.get(canon_sym) else {
                return Membership::Unsupported;
            };
            if t.sort() != info.sort {
                return Membership::Constrained(tm.mk_boolean(false));
            }
            let comp_ctx = CompCtx {
                tm,
                name_defs,
                distinct_preds,
            };
            let Some(applied) = encode_comp_expr(&info.body, &info.param, t.clone(), comp_ctx)
            else {
                return Membership::Unsupported;
            };
            let fixed_point = tm.mk_term(Kind::Equal, &[applied, t.clone()]);
            match membership_constraint(tm, t, lhs, name_defs, distinct_preds) {
                Membership::Unsupported => Membership::Unsupported,
                Membership::Unconstrained => Membership::Constrained(fixed_point),
                Membership::Constrained(in_lhs) => {
                    Membership::Constrained(tm.mk_term(Kind::And, &[in_lhs, fixed_point]))
                }
            }
        }

        _ => Membership::Unsupported,
    }
}
