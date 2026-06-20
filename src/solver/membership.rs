//! Set membership encoding — mapping Cantor set expressions to cvc5 predicates.

use cvc5::{Kind, Term, TermManager};

use crate::ast::{BinOp, Expr, ExprKind, UnOp};
use crate::span::Symbol;

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

        ExprKind::Comprehension { output, var, source, filter } => {
            comprehension_membership(tm, t, output, var, source, filter.as_deref())
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
            let Some(out_term) = encode_comp_expr(output, var, elem_term.clone(), tm) else {
                return Membership::Unsupported;
            };
            let eq = tm.mk_term(Kind::Equal, &[t.clone(), out_term]);
            if let Some(f) = filter {
                let Some(filter_term) = encode_comp_expr(f, var, elem_term, tm) else {
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
            let source_mem = membership_constraint(tm, t.clone(), source);
            let filter_mem = match filter {
                None => None,
                Some(f) => match encode_comp_expr(f, var, t.clone(), tm) {
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
) -> Option<Term<'tm>> {
    match &expr.kind {
        ExprKind::IntLit(n)  => Some(tm.mk_integer(*n)),
        ExprKind::BoolLit(b) => Some(tm.mk_boolean(*b)),
        ExprKind::Var(sym) if sym == var => Some(var_term),
        ExprKind::Var(_) => None, // free variable — not the bound var; unsupported
        ExprKind::UnOp { op, expr: inner } => {
            let t = encode_comp_expr(inner, var, var_term, tm)?;
            match op {
                UnOp::Neg => Some(tm.mk_term(Kind::Neg, &[t])),
                UnOp::Not => Some(tm.mk_term(Kind::Not, &[t])),
            }
        }
        ExprKind::BinOp { op, lhs, rhs } => {
            match op {
                BinOp::In | BinOp::NotIn => {
                    let l = encode_comp_expr(lhs, var, var_term.clone(), tm)?;
                    let mem = membership_constraint(tm, l, rhs);
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
            let l = encode_comp_expr(lhs, var, var_term.clone(), tm)?;
            let r = encode_comp_expr(rhs, var, var_term, tm)?;
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
    let lo  = tm.mk_integer(min);
    let hi  = tm.mk_integer(max);
    let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
    let leq = tm.mk_term(Kind::Leq, &[t, hi]);
    Membership::Constrained(tm.mk_term(Kind::And, &[geq, leq]))
}
