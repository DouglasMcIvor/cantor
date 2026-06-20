//! Set membership encoding — mapping Cantor set expressions to cvc5 predicates.

use cvc5::{Kind, Term, TermManager};

use crate::ast::{BinOp, Expr, ExprKind};

/// The result of asking "what does `t ∈ set_expr` look like as a cvc5 term?"
pub(crate) enum Membership<'tm> {
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
pub(crate) fn membership_constraint<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    set_expr: &Expr,
) -> Membership<'tm> {
    match &set_expr.kind {
        ExprKind::Var(sym) => match sym.0.as_str() {
            "Int"        => Membership::Unconstrained,
            // Fail is the out-of-band failure sentinel — no integer value is ever
            // in Fail.  Constrained(false) means "this predicate never holds for
            // an integer t", which causes Nat | Fail to simplify to Nat >= 0
            // correctly: (t >= 0) || false = (t >= 0).
            "Fail"       => Membership::Constrained(tm.mk_boolean(false)),
            "Nat"        => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Geq, &[t, zero]))
            }
            "NatPos"     => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Gt, &[t, zero]))
            }
            "NonZeroInt" => {
                let zero = tm.mk_integer(0);
                Membership::Constrained(tm.mk_term(Kind::Distinct, &[t, zero]))
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

pub(crate) fn bounded<'tm>(tm: &'tm TermManager, t: Term<'tm>, min: i64, max: i64) -> Membership<'tm> {
    let lo  = tm.mk_integer(min);
    let hi  = tm.mk_integer(max);
    let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
    let leq = tm.mk_term(Kind::Leq, &[t, hi]);
    Membership::Constrained(tm.mk_term(Kind::And, &[geq, leq]))
}
