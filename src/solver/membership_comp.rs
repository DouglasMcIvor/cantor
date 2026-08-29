//! Comprehension membership encoding — split from `membership.rs` to keep
//! that file under 1000 lines.
//!
//! `comprehension_membership`, `encode_comp_expr`, and `encode_comp_arith`
//! are a mutually recursive cluster with their own private `SemExpr`
//! sub-language (arithmetic + comparisons over one bound variable) — a
//! self-contained concern distinct from `membership_constraint`'s structural
//! recursion over set-algebra operators.

use cvc5::{Kind, Term, TermManager};

use crate::ast::{BinOp, UnOp};
use crate::semantics::tree::{SemExpr, SemExprKind};
use crate::span::Symbol;

use super::NameDefs;
use super::encode_call::{mk_domain_sort, named_union_arm_for_constructor};
use super::membership::{Membership, SolverPreds, membership_constraint};

/// The solver-wide pieces shared, unchanged, by `comprehension_membership`,
/// `encode_comp_expr`, and `encode_comp_arith` — all `Copy` shared
/// references, so this bundle can just be passed by value throughout their
/// mutual recursion.
#[derive(Clone, Copy)]
pub(crate) struct CompCtx<'a, 'tm> {
    pub(crate) tm: &'tm TermManager,
    pub(crate) name_defs: &'a NameDefs,
    pub(crate) distinct_preds: &'a SolverPreds<'tm>,
}

/// Encode `t ∈ { output for var in source if filter }` as a cvc5 predicate.
///
/// Two strategies:
/// - Finite literal source: unroll into a disjunction of equalities (one per element).
/// - Identity output (`{x for x in S if P(x)}`): encode as `t ∈ S ∧ P(t)`.
/// - All other cases: `Unsupported` (Unknown at the solver level).
pub(crate) fn comprehension_membership<'tm>(
    t: Term<'tm>,
    output: &SemExpr,
    var: &Symbol,
    source: &SemExpr,
    filter: Option<&SemExpr>,
    ctx: CompCtx<'_, 'tm>,
) -> Membership<'tm> {
    let tm = ctx.tm;
    // Case 1: source is a finite set literal — unroll.
    if let SemExprKind::SetLit(elements) = &source.kind {
        if elements.is_empty() {
            return Membership::Constrained(tm.mk_boolean(false));
        }
        let mut disjuncts: Vec<Term<'_>> = Vec::new();
        for elem in elements {
            let SemExprKind::IntLit(n) = &elem.kind else {
                return Membership::Unsupported;
            };
            let elem_term = tm.mk_integer(*n);
            let Some(out_term) = encode_comp_expr(output, var, elem_term.clone(), ctx) else {
                return Membership::Unsupported;
            };
            let eq = tm.mk_term(Kind::Equal, &[t.clone(), out_term]);
            if let Some(f) = filter {
                let Some(filter_term) = encode_comp_expr(f, var, elem_term, ctx) else {
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
    if let SemExprKind::Var(sym) = &output.kind
        && sym == var
    {
        let source_mem =
            membership_constraint(tm, t.clone(), source, ctx.name_defs, ctx.distinct_preds);
        let filter_mem = match filter {
            None => None,
            Some(f) => match encode_comp_expr(f, var, t.clone(), ctx) {
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

    Membership::Unsupported
}

/// Encode a Cantor expression as a cvc5 term, substituting `var_term` for the
/// bound variable `var`.  Only handles arithmetic and comparisons — enough for
/// comprehension output expressions and filter predicates.  Returns `None` for
/// anything more complex (calls, if-then-else, etc.).
pub(crate) fn encode_comp_expr<'tm>(
    expr: &SemExpr,
    var: &Symbol,
    var_term: Term<'tm>,
    ctx: CompCtx<'_, 'tm>,
) -> Option<Term<'tm>> {
    let tm = ctx.tm;
    match &expr.kind {
        SemExprKind::IntLit(n) => Some(tm.mk_integer(*n)),
        SemExprKind::BoolLit(b) => Some(tm.mk_boolean(*b)),
        SemExprKind::Var(sym) if sym == var => Some(var_term),
        SemExprKind::Var(_) => None, // free variable — not the bound var; unsupported
        SemExprKind::UnOp { op, expr: inner } => {
            let t = encode_comp_expr(inner, var, var_term, ctx)?;
            match op {
                UnOp::Neg => Some(tm.mk_term(Kind::Neg, &[t])),
                UnOp::Not => Some(tm.mk_term(Kind::Not, &[t])),
            }
        }
        // `output`/`filter` are value-position (elaborate_expr elaborates a
        // comprehension's output/filter under Position::Value), so `+ - * /`
        // are the dedicated arithmetic variants here, never DisjointUnion/etc.
        SemExprKind::Add(lhs, rhs) => encode_comp_arith(Kind::Add, lhs, rhs, var, var_term, ctx),
        SemExprKind::Sub(lhs, rhs) => encode_comp_arith(Kind::Sub, lhs, rhs, var, var_term, ctx),
        SemExprKind::Mul(lhs, rhs) => encode_comp_arith(Kind::Mult, lhs, rhs, var, var_term, ctx),
        SemExprKind::Div(lhs, rhs) => {
            encode_comp_arith(Kind::IntsDivision, lhs, rhs, var, var_term, ctx)
        }
        SemExprKind::BinOp { op, lhs, rhs } => {
            match op {
                BinOp::In | BinOp::NotIn => {
                    let l = encode_comp_expr(lhs, var, var_term.clone(), ctx)?;
                    let mem = membership_constraint(tm, l, rhs, ctx.name_defs, ctx.distinct_preds);
                    return match (op, mem) {
                        (BinOp::In, Membership::Constrained(c)) => Some(c),
                        (BinOp::In, Membership::Unconstrained) => Some(tm.mk_boolean(true)),
                        (BinOp::NotIn, Membership::Constrained(c)) => {
                            Some(tm.mk_term(Kind::Not, &[c]))
                        }
                        (BinOp::NotIn, Membership::Unconstrained) => Some(tm.mk_boolean(false)),
                        _ => None,
                    };
                }
                _ => {}
            }
            let l = encode_comp_expr(lhs, var, var_term.clone(), ctx)?;
            let r = encode_comp_expr(rhs, var, var_term, ctx)?;
            let kind = match op {
                BinOp::Eq => Kind::Equal,
                BinOp::Ne => Kind::Distinct,
                BinOp::Lt => Kind::Lt,
                BinOp::Le => Kind::Leq,
                BinOp::Gt => Kind::Gt,
                BinOp::Ge => Kind::Geq,
                BinOp::And => Kind::And,
                BinOp::Or => Kind::Or,
                BinOp::In | BinOp::NotIn => unreachable!("handled above"),
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => unreachable!(
                    "Add/Sub/Mul/Div are dedicated SemExprKind variants, never wrapped in BinOp"
                ),
                BinOp::Rem => Kind::IntsModulus,
                BinOp::Quot => Kind::IntsDivision,
                // `Arrow` is set-position only (a function Kind) and never
                // elaborated into a value-producing `SemExprKind::BinOp` —
                // see `solver::encode`'s matching arm.
                BinOp::Union
                | BinOp::Intersect
                | BinOp::SymDiff
                | BinOp::Concat
                | BinOp::Arrow
                | BinOp::Compose => {
                    return None;
                }
            };
            Some(tm.mk_term(kind, &[l, r]))
        }
        // `from(x)` — one of two `Call` shapes a comprehension filter
        // supports. No general `Call` support: `from` is the only ordinary
        // builtin whose solver encoding is a single `ApplyUf` with no extra
        // obligations of its own, so it's safe to inline here. `x`'s
        // distinct set isn't known syntactically at this point — found by
        // matching `arg_term`'s own sort against the registered
        // `DistinctInfo`s (each distinct set's sort is unique, so this is
        // never ambiguous).
        SemExprKind::Call { callee, args } if callee.0 == "from" && args.len() == 1 => {
            let arg_term = encode_comp_expr(&args[0], var, var_term, ctx)?;
            let info = ctx
                .distinct_preds
                .values()
                .find(|info| info.sort == arg_term.sort())?;
            Some(tm.mk_term(Kind::ApplyUf, &[info.from.clone(), arg_term]))
        }
        // `{Union}.{Label}?(x)` / `{Union}.{Label}!(x)` — the other supported
        // `Call` shapes: a constructor pattern's synthesized domain-
        // narrowing tester and payload extractor (pattern-matching plan
        // step 4/4, `semantics::elaborate::desugar_param_patterns`/
        // `ctor_pattern_tester_callee`/`ctor_pattern_extractor_callee`).
        // Same reasoning as `from(x)` above (`ApplyUf` + `ApplyTester`/
        // `ApplySelector`, no extra obligations of their own), and this is
        // the *only* place a constructor-pattern's domain filter is ever
        // solver-encoded — both the per-call membership check and
        // `disjointness.rs`'s overload-disjointness proof go through
        // `comprehension_membership`'s identity-output path, which calls
        // this function for the filter. The extractor needs to appear here
        // (not just in value position, where `encode_call.rs`'s own copy of
        // this logic handles it) because `desugar_param_patterns` folds an
        // `extractor(x) in <arm's own basis>` conjunct into the filter
        // itself — a fresh symbolic domain parameter otherwise carries no
        // fact at all about its extracted payload (the basis obligation is
        // normally only ever asserted at a labeled constructor's own call
        // site, never as a blanket axiom over the whole union sort), which
        // made every non-trivial constructor-pattern body a false
        // counterexample (e.g. `area(Shape.Circle(r)) = r * r` — nothing
        // told the solver `r`'s arbitrary extracted value was even
        // non-negative).
        SemExprKind::Call { callee, args } if args.len() == 1 => {
            let (bare_callee, is_tester) = match callee.0.strip_suffix('?') {
                Some(b) => (b, true),
                None => (callee.0.strip_suffix('!')?, false),
            };
            let (union_def, arm_idx, _arm_expr) =
                named_union_arm_for_constructor(&Symbol::new(bare_callee), ctx.name_defs)?;
            let info = ctx.distinct_preds.get(&union_def.name)?;
            let arg_term = encode_comp_expr(&args[0], var, var_term, ctx)?;
            let unwrapped = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), arg_term]);
            let dt = mk_domain_sort(info).datatype();
            let ctor = dt.constructor(arm_idx);
            Some(if is_tester {
                tm.mk_term(Kind::ApplyTester, &[ctor.tester_term(), unwrapped])
            } else {
                tm.mk_term(Kind::ApplySelector, &[ctor.selector(0).term(), unwrapped])
            })
        }
        _ => None, // Call (other than `from`/a ctor-pattern tester/extractor), If, Try, SetLit, Comprehension — unsupported
    }
}

fn encode_comp_arith<'tm>(
    kind: Kind,
    lhs: &SemExpr,
    rhs: &SemExpr,
    var: &Symbol,
    var_term: Term<'tm>,
    ctx: CompCtx<'_, 'tm>,
) -> Option<Term<'tm>> {
    let l = encode_comp_expr(lhs, var, var_term.clone(), ctx)?;
    let r = encode_comp_expr(rhs, var, var_term, ctx)?;
    Some(ctx.tm.mk_term(kind, &[l, r]))
}
