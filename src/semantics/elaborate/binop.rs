//! Elaboration of `BinOp` nodes — the Value/Set duality of `+ - * /`, `in`/`not
//! in`'s local-set-variable special case, set operations, `++`, and the
//! remaining single-meaning comparisons/logical operators.

use crate::ast::{BinOp, Expr, ExprKind};
use crate::error::CompileError;
use crate::kind::Kind;
use crate::semantics::tree::*;
use crate::span::Span;

use super::{Ctx, Env, Position, elaborate_expr, not_yet_implemented};

/// The pieces of one `BinOp` node `elaborate_binop` needs — bundled per the
/// project's context-struct convention for a function that would otherwise
/// take too many arguments (all "same cluster, varies per call", not several
/// unrelated concerns).
#[derive(Clone, Copy)]
pub(super) struct BinOpNode<'a> {
    pub(super) expr: &'a Expr,
    pub(super) op: &'a BinOp,
    pub(super) lhs: &'a Expr,
    pub(super) rhs: &'a Expr,
    pub(super) pos: Position,
    pub(super) span: Span,
}

pub(super) fn elaborate_binop(
    node: BinOpNode,
    ctx: &Ctx,
    env: &mut Env,
) -> Result<SemExpr, CompileError> {
    let BinOpNode {
        expr,
        op,
        lhs,
        rhs,
        pos,
        span,
    } = node;
    let kind_of_for_set = || crate::kind::set_kind(expr, ctx.name_defs);

    match op {
        BinOp::Add => {
            let (l, r) = (
                elaborate_expr(lhs, pos, ctx, env)?,
                elaborate_expr(rhs, pos, ctx, env)?,
            );
            let (node, kind_of) = match pos {
                Position::Value => {
                    let kind_of = arith_value_kind(&l.kind_of, &r.kind_of);
                    (SemExprKind::Add(Box::new(l), Box::new(r)), kind_of)
                }
                Position::Set => (
                    SemExprKind::DisjointUnion(Box::new(l), Box::new(r)),
                    kind_of_for_set()?,
                ),
            };
            Ok(SemExpr {
                kind: node,
                kind_of,
                span,
            })
        }
        BinOp::Sub => {
            let (l, r) = (
                elaborate_expr(lhs, pos, ctx, env)?,
                elaborate_expr(rhs, pos, ctx, env)?,
            );
            let (node, kind_of) = match pos {
                Position::Value => {
                    let kind_of = arith_value_kind(&l.kind_of, &r.kind_of);
                    (SemExprKind::Sub(Box::new(l), Box::new(r)), kind_of)
                }
                Position::Set => (
                    SemExprKind::SetDifference(Box::new(l), Box::new(r)),
                    kind_of_for_set()?,
                ),
            };
            Ok(SemExpr {
                kind: node,
                kind_of,
                span,
            })
        }
        BinOp::Mul => {
            let (l, r) = (
                elaborate_expr(lhs, pos, ctx, env)?,
                elaborate_expr(rhs, pos, ctx, env)?,
            );
            let (node, kind_of) = match pos {
                Position::Value => {
                    let kind_of = arith_value_kind(&l.kind_of, &r.kind_of);
                    (SemExprKind::Mul(Box::new(l), Box::new(r)), kind_of)
                }
                Position::Set => (
                    SemExprKind::CartesianProduct(Box::new(l), Box::new(r)),
                    kind_of_for_set()?,
                ),
            };
            Ok(SemExpr {
                kind: node,
                kind_of,
                span,
            })
        }
        BinOp::Div => {
            let l = elaborate_expr(lhs, pos, ctx, env)?;
            let (node, kind_of) = match pos {
                Position::Value => {
                    let r = elaborate_expr(rhs, pos, ctx, env)?;
                    (SemExprKind::Div(Box::new(l), Box::new(r)), Kind::Int)
                }
                // `L / canon` — quotient-set formation. Unlike `+ - *`'s
                // Set-position duals, the RHS here is never itself a set
                // description: it's a reference to a named canonicalizer
                // function, so it's rejected/accepted by raw AST shape
                // (a bare name) rather than elaborated as an expression —
                // elaborating it via `elaborate_expr(rhs, Position::Set, ..)`
                // would try (and fail) to resolve it as a *set* name, since
                // functions never appear in `name_defs`. Resolving the
                // symbol against its actual function body is deferred to
                // solver time (`build_quotient_preds`), once `fn_env` exists.
                Position::Set => {
                    let ExprKind::Var(canon_sym) = &rhs.kind else {
                        return Err(CompileError::InvalidSetExpression {
                            detail: "canonicalizer must be a named function \
                                     (lambdas not yet supported)"
                                .to_string(),
                            span: rhs.span,
                        });
                    };
                    (
                        SemExprKind::SetQuotient(Box::new(l), canon_sym.clone()),
                        kind_of_for_set()?,
                    )
                }
            };
            Ok(SemExpr {
                kind: node,
                kind_of,
                span,
            })
        }

        // `in`/`not in`: the RHS is normally a set *description* regardless of
        // the position the `in` expression itself appears in (mirrors
        // compile_membership / membership_constraint). But when the RHS is a
        // local variable already bound to a genuine runtime `Kind::Set(_)`
        // value (e.g. `mut s : Set(Int) = {...}`), it's a value lookup
        // instead — mirrors codegen::compile_binop's own dispatch (env
        // lookup first, set-description fallback second). Using Position::Set
        // unconditionally would call `set_kind` on a local name and panic
        // with "unknown set name".
        BinOp::In | BinOp::NotIn => {
            let l = elaborate_expr(lhs, Position::Value, ctx, env)?;
            let rhs_is_local_set_var = matches!(&rhs.kind, ExprKind::Var(sym)
                if matches!(env.get(sym), Some(Kind::Set(_))));
            let rhs_pos = if rhs_is_local_set_var {
                Position::Value
            } else {
                Position::Set
            };
            let r = elaborate_expr(rhs, rhs_pos, ctx, env)?;
            Ok(SemExpr {
                kind: SemExprKind::BinOp {
                    op: *op,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                },
                kind_of: Kind::Bool,
                span,
            })
        }

        BinOp::Union | BinOp::Intersect | BinOp::SymDiff => {
            let (l, r) = (
                elaborate_expr(lhs, pos, ctx, env)?,
                elaborate_expr(rhs, pos, ctx, env)?,
            );
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                // codegen::compile_binop rejects these outright in value
                // position today ("set operations not yet implemented").
                Position::Value => {
                    return Err(not_yet_implemented(
                        &format!("`{op}` in value position"),
                        span,
                    ));
                }
            };
            Ok(SemExpr {
                kind: SemExprKind::BinOp {
                    op: *op,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                },
                kind_of,
                span,
            })
        }

        BinOp::Concat => {
            let l = elaborate_expr(lhs, Position::Value, ctx, env)?;
            let r = elaborate_expr(rhs, Position::Value, ctx, env)?;
            let (_, kind_of) = crate::kind::merge_concat_kinds(&l.kind_of, &r.kind_of)
                .map_err(|e| CompileError::ice(e))?;
            Ok(SemExpr {
                kind: SemExprKind::BinOp {
                    op: BinOp::Concat,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                },
                kind_of,
                span,
            })
        }

        // `rem`/`quot` — arithmetic-only, single meaning (Int), Value
        // position only. Unlike `+ - * /` they have no set-forming dual
        // (no "SetRem"/"SetQuot" concept), so Set position is a hard user
        // error rather than a silent Kind::Int default.
        BinOp::Rem | BinOp::Quot => match pos {
            Position::Value => {
                let l = elaborate_expr(lhs, pos, ctx, env)?;
                let r = elaborate_expr(rhs, pos, ctx, env)?;
                Ok(SemExpr {
                    kind: SemExprKind::BinOp {
                        op: *op,
                        lhs: Box::new(l),
                        rhs: Box::new(r),
                    },
                    kind_of: Kind::Int,
                    span,
                })
            }
            Position::Set => Err(CompileError::InvalidSetExpression {
                detail: format!(
                    "`{op}` is arithmetic-only and has no set-forming meaning \
                     (unlike `+ - * /`, which are disjoint union / set \
                     difference / Cartesian product / set quotient in set \
                     position)"
                ),
                span,
            }),
        },

        _ => {
            // Remaining operators: comparisons and logical and/or — single
            // meaning (Bool) regardless of position.
            let l = elaborate_expr(lhs, pos, ctx, env)?;
            let r = elaborate_expr(rhs, pos, ctx, env)?;
            // Operand-kind agreement, value position only (in set position the
            // operands are set descriptions, reserved for subset comparisons).
            // Without this check the mismatch reaches cvc5 as an ill-sorted
            // term and aborts the whole process with a raw C++ error.
            if pos == Position::Value {
                match op {
                    BinOp::Eq | BinOp::Ne if l.kind_of != r.kind_of => {
                        return Err(CompileError::ice(format!(
                            "`{op}` requires both operands from the same value family, \
                             got {:?} and {:?} — e.g. Bool and Int are disjoint in \
                             Cantor's value model (`true` is not `1`); convert \
                             explicitly with `if b then 1 else 0` if that is what \
                             you meant",
                            l.kind_of, r.kind_of
                        )));
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                        if !is_ordered_pair(&l.kind_of, &r.kind_of) =>
                    {
                        let chained_hint = if l.kind_of == Kind::Bool {
                            " (a chain like `a < b < c` parses as `(a < b) < c`; \
                             write `a < b and b < c` instead)"
                        } else {
                            ""
                        };
                        return Err(CompileError::ice(format!(
                            "`{op}` compares Int, Signed32, or Unsigned32 (both operands \
                             the same one of those), got {:?} and {:?} — Bool is not \
                             ordered, and Signed32/Unsigned32 are disjoint from Int and \
                             from each other{chained_hint}",
                            l.kind_of, r.kind_of
                        )));
                    }
                    _ => {}
                }
            }
            Ok(SemExpr {
                kind: SemExprKind::BinOp {
                    op: *op,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                },
                kind_of: Kind::Bool,
                span,
            })
        }
    }
}

/// Value-position `+ - *`'s result Kind: `Int` for every combination except
/// two matching wrapping operands, which stay in their own family (no
/// arithmetic Kind ever silently becomes `Int` — that would tell codegen to
/// treat an i32 register as the tagged i64 `Int` wire type). A genuine
/// mismatch (e.g. `Signed32 + Int`) falls through to plain `Kind::Int` here,
/// same as it always has for any other Kind combination — it's still
/// rejected, just later, by the solver's existing sort-mismatch guard
/// (`Membership::Constrained(false)`), exactly like today's `distinct`
/// values in raw arithmetic (docs/wrapping-and-quotient-sets-plan.md).
fn arith_value_kind(l: &Kind, r: &Kind) -> Kind {
    if l == r && matches!(l, Kind::Signed32 | Kind::Unsigned32) {
        l.clone()
    } else {
        Kind::Int
    }
}

/// Whether `<`/`<=`/`>`/`>=` accepts this operand pair: both sides the same
/// ordered-scalar Kind. `Signed32`/`Unsigned32` are ordered (comparisons pick
/// `bvslt`/`bvult` per family at the solver layer) but mutually disjoint —
/// `Signed32 < Unsigned32` is rejected here just like `Bool < Int` always
/// was, not silently accepted by falling back to `Int`'s comparison.
fn is_ordered_pair(l: &Kind, r: &Kind) -> bool {
    l == r && matches!(l, Kind::Int | Kind::Signed32 | Kind::Unsigned32)
}
