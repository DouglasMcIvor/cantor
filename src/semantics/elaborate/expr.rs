//! Elaboration of expressions other than `BinOp` (see `binop.rs`): literals,
//! variable lookup, unary operators, calls, `if`, set/tuple literals, `try`/
//! `fail with`, comprehensions, projection/indexing, and `X*`.

use crate::ast::{self, ExprKind, UnOp};
use crate::error::CompileError;
use crate::kind::{self, Kind, set_kind};
use crate::semantics::tree::*;

use super::{Ctx, Env, Position, builtin_call_kind, not_yet_implemented};

pub(super) fn elaborate_expr(
    expr: &ast::Expr,
    pos: Position,
    ctx: &Ctx,
    env: &mut Env,
) -> Result<SemExpr, CompileError> {
    let span = expr.span;

    // Set-position nodes: `set_kind` already implements every one of these
    // rules correctly (that's its sole purpose) and is exercised by the
    // existing kind_tests/solver/codegen suites, so kind_of is looked up
    // directly from the original AST node instead of re-derived here.
    let kind_of_for_set = || set_kind(expr, ctx.name_defs);

    match &expr.kind {
        ExprKind::IntLit(n) => Ok(SemExpr {
            kind: SemExprKind::IntLit(*n),
            kind_of: Kind::Int,
            span,
        }),
        ExprKind::BoolLit(b) => Ok(SemExpr {
            kind: SemExprKind::BoolLit(*b),
            kind_of: Kind::Bool,
            span,
        }),
        ExprKind::CharLit(c) => Ok(SemExpr {
            kind: SemExprKind::CharLit(*c),
            kind_of: Kind::Char,
            span,
        }),
        ExprKind::FailLit => Ok(SemExpr {
            kind: SemExprKind::FailLit,
            // Matches codegen::compile_expr exactly: at runtime `fail` is the
            // {tag, i64} fallible-return wrapper, not the bare Fail singleton
            // that `set_kind` uses for set-position membership checks.
            kind_of: Kind::Tuple(vec![Kind::Fail, Kind::Int]),
            span,
        }),
        ExprKind::NoneLit => Ok(SemExpr {
            kind: SemExprKind::NoneLit,
            // Mirrors FailLit exactly, using `None`'s own marker — see
            // `kind::is_propagation_tuple`.
            kind_of: Kind::Tuple(vec![Kind::None, Kind::Int]),
            span,
        }),

        ExprKind::Var(sym) => {
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                // A local (param/let) takes priority; falling through to
                // `name_defs` covers a value-position reference to a
                // top-level scalar constant (e.g. `base : Nat = 10` used in
                // another function's body) — mirrors `set_kind`'s own
                // `Var` fallback, reused here since Kind doesn't depend on
                // position for a name lookup, only *whether* it's local.
                Position::Value => match env.get(sym) {
                    Some(k) => k.clone(),
                    None => {
                        let def = ctx.name_defs.get(sym).ok_or_else(|| {
                            CompileError::ice(format!(
                                "elaborate: reference to undefined local `{}`",
                                sym.0
                            ))
                        })?;
                        match def.kind {
                            ast::DefKind::Alias => set_kind(&def.value, ctx.name_defs)?,
                            ast::DefKind::Distinct => Kind::Int,
                        }
                    }
                },
            };
            Ok(SemExpr {
                kind: SemExprKind::Var(sym.clone()),
                kind_of,
                span,
            })
        }

        ExprKind::BinOp { op, lhs, rhs } => super::binop::elaborate_binop(
            super::binop::BinOpNode {
                expr,
                op,
                lhs,
                rhs,
                pos,
                span,
            },
            ctx,
            env,
        ),

        ExprKind::UnOp {
            op: UnOp::Not,
            expr: inner,
        } => {
            let e = elaborate_expr(inner, pos, ctx, env)?;
            Ok(SemExpr {
                kind: SemExprKind::UnOp {
                    op: UnOp::Not,
                    expr: Box::new(e),
                },
                kind_of: Kind::Bool,
                span,
            })
        }
        ExprKind::UnOp {
            op: UnOp::Neg,
            expr: inner,
        } => {
            let e = elaborate_expr(inner, pos, ctx, env)?;
            // Matches set_kind (passes through) in set position. In value
            // position, negation stays within the operand's own family —
            // `Signed32`/`Unsigned32` negate via `bvneg` and never become a
            // tagged `Kind::Int` (docs/wrapping-and-quotient-sets-plan.md) —
            // and defaults to `Int` otherwise, same as always.
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                Position::Value => match e.kind_of {
                    Kind::Signed32 | Kind::Unsigned32 => e.kind_of.clone(),
                    _ => Kind::Int,
                },
            };
            Ok(SemExpr {
                kind: SemExprKind::UnOp {
                    op: UnOp::Neg,
                    expr: Box::new(e),
                },
                kind_of,
                span,
            })
        }

        ExprKind::Call { callee, args }
            if callee.0 == crate::semantics::builtins::SET_CONSTRUCTOR && args.len() == 1 =>
        {
            // Built-in `Set(X)` constructor — its argument is always a set
            // description, regardless of the call's own position.
            let arg = elaborate_expr(&args[0], Position::Set, ctx, env)?;
            Ok(SemExpr {
                kind: SemExprKind::Call {
                    callee: callee.clone(),
                    args: vec![arg],
                },
                kind_of: kind_of_for_set()?,
                span,
            })
        }
        // Any other call reached in set position is meaningless — the only
        // legitimate set-position call is the `Set(X)` arm above. Mirrors
        // `kind::set_kind`'s own fallback exactly; caught here before the
        // generic arm below, which would otherwise elaborate `args` as
        // values and report a confusing "undefined local" error pointing at
        // an argument instead of the actually-undefined callee.
        ExprKind::Call { callee, .. } if pos == Position::Set => {
            Err(CompileError::UndefinedFunction {
                name: callee.0.clone(),
                span,
            })
        }
        ExprKind::Call { callee, args } => {
            let sem_args = args
                .iter()
                .map(|a| elaborate_expr(a, Position::Value, ctx, env))
                .collect::<Result<Vec<_>, _>>()?;
            // `from`/`size`/`len`/auto-generated `distinct` constructors are
            // recognized directly by name in codegen::compile_call — they're
            // never user-declared functions, so they'd never appear in
            // `fn_sigs`. Mirrors that special-casing exactly.
            let kind_of = if let Some(k) = builtin_call_kind(callee, sem_args.len(), ctx.name_defs)
            {
                k
            } else {
                ctx.fn_sigs
                    .get(callee)
                    .map(|s| s.return_kind.clone())
                    .ok_or_else(|| CompileError::UndefinedFunction {
                        name: callee.0.clone(),
                        span,
                    })?
            };
            Ok(SemExpr {
                kind: SemExprKind::Call {
                    callee: callee.clone(),
                    args: sem_args,
                },
                kind_of,
                span,
            })
        }

        ExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            let c = elaborate_expr(cond, Position::Value, ctx, env)?;
            if c.kind_of != Kind::Bool {
                return Err(CompileError::ice(format!(
                    "if-condition must be Bool, got {:?} — Bool and Int are disjoint in \
                     Cantor's value model, so a value from e.g. a `Bool | Int`-family union \
                     cannot be used as a condition without narrowing it explicitly first",
                    c.kind_of
                )));
            }
            let t = elaborate_expr(then_expr, pos, ctx, env)?;
            let e = elaborate_expr(else_expr, pos, ctx, env)?;
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                Position::Value => crate::kind::merge_if_branches(&t.kind_of, &e.kind_of)
                    .map(|merge| merge.result_kind())
                    .map_err(|e| CompileError::ice(e))?,
            };
            Ok(SemExpr {
                kind: SemExprKind::If {
                    cond: Box::new(c),
                    then_expr: Box::new(t),
                    else_expr: Box::new(e),
                },
                kind_of,
                span,
            })
        }

        ExprKind::SetLit(elements) => {
            // Elements of `{v1, v2, ...}` are concrete member *values* (e.g.
            // `{[]}`'s `[]` is the empty-vector value, not a set expression),
            // regardless of whether the SetLit itself sits in set position.
            let sem_elements = elements
                .iter()
                .map(|e| elaborate_expr(e, Position::Value, ctx, env))
                .collect::<Result<Vec<_>, _>>()?;
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                Position::Value => {
                    // Matches compile_set_lit_value: a non-empty, homogeneous
                    // literal of a scalar Kind constructs a genuine runtime
                    // Set value.
                    let Some(first) = sem_elements.first() else {
                        return Err(CompileError::ice(
                            "empty set literal in value position — element kind cannot be \
                             inferred; add an explicit annotation",
                        ));
                    };
                    if !crate::kind::is_scalar_word_kind(&first.kind_of) {
                        return Err(CompileError::Unsupported {
                            feature: format!(
                                "Set({:?}) — runtime sets can only hold scalar elements \
                                 (Int, Bool, Fail, and their named subsets) today",
                                first.kind_of
                            ),
                            span,
                        });
                    }
                    if sem_elements.iter().any(|e| e.kind_of != first.kind_of) {
                        return Err(CompileError::ice("mixed element kinds in set literal"));
                    }
                    Kind::Set(Box::new(first.kind_of.clone()))
                }
            };
            Ok(SemExpr {
                kind: SemExprKind::SetLit(sem_elements),
                kind_of,
                span,
            })
        }

        ExprKind::Try(inner) => {
            let e = elaborate_expr(inner, pos, ctx, env)?;
            // Matches compile_try exactly: always the unwrapped Int payload.
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                Position::Value => Kind::Int,
            };
            Ok(SemExpr {
                kind: SemExprKind::Try(Box::new(e)),
                kind_of,
                span,
            })
        }

        ExprKind::FailWith(inner) => {
            let e = elaborate_expr(inner, Position::Value, ctx, env)?;
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                // Matches compile_expr exactly: always the fallible wrapper,
                // regardless of the payload expression's own Kind.
                Position::Value => Kind::Tuple(vec![Kind::Fail, Kind::Int]),
            };
            Ok(SemExpr {
                kind: SemExprKind::FailWith(Box::new(e)),
                kind_of,
                span,
            })
        }

        ExprKind::Comprehension {
            output,
            var,
            source,
            filter,
        } => {
            if pos == Position::Value {
                // codegen rejects this outright today ("comprehension in
                // value position not yet supported") — comprehensions are
                // set-expression-position only per the v0 design.
                return Err(not_yet_implemented("comprehension in value position", span));
            }
            let src = elaborate_expr(source, Position::Set, ctx, env)?;
            env.insert(var.clone(), src.kind_of.clone());
            let out = elaborate_expr(output, Position::Value, ctx, env)?;
            let filt = filter
                .as_ref()
                .map(|f| elaborate_expr(f, Position::Value, ctx, env))
                .transpose()?;
            env.remove(var);
            Ok(SemExpr {
                kind: SemExprKind::Comprehension {
                    output: Box::new(out),
                    var: var.clone(),
                    source: Box::new(src),
                    filter: filt.map(Box::new),
                },
                kind_of: kind_of_for_set()?,
                span,
            })
        }

        ExprKind::Tuple(elements) => {
            if pos == Position::Set {
                return Err(CompileError::InvalidSetExpression {
                    detail: "a tuple/array literal `(a, b, ...)` / `[a, b, ...]` cannot be \
                             used as a set expression here — write a Cartesian product with \
                             `*` instead (e.g. `Int * Int`)"
                        .to_string(),
                    span,
                });
            }
            let sem_elements = elements
                .iter()
                .map(|e| elaborate_expr(e, pos, ctx, env))
                .collect::<Result<Vec<_>, _>>()?;
            let kind_of = Kind::Tuple(sem_elements.iter().map(|e| e.kind_of.clone()).collect());
            Ok(SemExpr {
                kind: SemExprKind::Tuple(sem_elements),
                kind_of,
                span,
            })
        }

        ExprKind::Proj { base, index } => {
            let b = elaborate_expr(base, pos, ctx, env)?;
            let kind_of = proj_kind(&b.kind_of, *index)?;
            Ok(SemExpr {
                kind: SemExprKind::Proj {
                    base: Box::new(b),
                    index: *index,
                },
                kind_of,
                span,
            })
        }

        ExprKind::Index { base, index } => {
            let b = elaborate_expr(base, pos, ctx, env)?;
            let i = elaborate_expr(index, Position::Value, ctx, env)?;
            let seq_unification_ek = match &b.kind_of {
                Kind::TaggedUnion(arms) => kind::sequence_unification_elem_kind(arms),
                _ => None,
            };
            let kind_of = match (&b.kind_of, seq_unification_ek) {
                (Kind::Vector(ek), _) => vector_elem_kind(ek)?,
                (_, Some(ek)) => ek,
                (other, None) => {
                    return Err(CompileError::ice(format!(
                        "`[i]` requires a vector (X*) base, got {other:?}"
                    )));
                }
            };
            Ok(SemExpr {
                kind: SemExprKind::Index {
                    base: Box::new(b),
                    index: Box::new(i),
                },
                kind_of,
                span,
            })
        }

        ExprKind::KleeneStar(inner) => {
            if pos == Position::Value {
                // codegen rejects this outright today ("X* is a set
                // expression and cannot appear in value position").
                return Err(CompileError::ice(
                    "X* is a set expression and cannot appear in value position",
                ));
            }
            let e = elaborate_expr(inner, Position::Set, ctx, env)?;
            let kind_of = Kind::Vector(Box::new(e.kind_of.clone()));
            Ok(SemExpr {
                kind: SemExprKind::KleeneStar(Box::new(e)),
                kind_of,
                span,
            })
        }
    }
}

/// `.N` projection's resulting Kind — mirrors `compile_proj`'s simple cases
/// (plain Tuple, TaggedUnion leaves). Vector-of-Tuple/TaggedUnion bases are
/// real codegen capability not yet re-derived here (see module docs).
fn proj_kind(base_kind: &Kind, index: usize) -> Result<Kind, CompileError> {
    match base_kind {
        Kind::Tuple(elems) => elems.get(index).cloned().ok_or_else(|| {
            CompileError::ice(format!(
                "tuple index {index} out of bounds (tuple has {} elements)",
                elems.len()
            ))
        }),
        // A sequence-unification union (e.g. `Nat* ^ Int`) reinterprets `.N`
        // as sequence indexing; any other TaggedUnion falls back to raw LLVM
        // leaf N (the union's leaves are always plain i64/`Kind::Int`).
        Kind::TaggedUnion(arms) => {
            Ok(kind::sequence_unification_elem_kind(arms).unwrap_or(Kind::Int))
        }
        Kind::Vector(ek) => vector_elem_kind(ek),
        other => Err(CompileError::ice(format!(
            "projection `.{index}` applied to non-tuple value {other:?}"
        ))),
    }
}

/// `Vector(ek)`'s element Kind for `[i]`/`.N` indexing. `codegen::expr_vec`
/// dispatches to different runtime helpers per element Kind (scalar Arrow
/// arrays vs. `cantor_struct_vec_*`/`cantor_union_vec_*` for `Tuple`/
/// `TaggedUnion` elements), but every one of those helpers reassembles the
/// *same* element Kind it was given — indexing never changes the Kind.
fn vector_elem_kind(ek: &Kind) -> Result<Kind, CompileError> {
    match ek {
        Kind::Int | Kind::Bool | Kind::Vector(_) | Kind::Tuple(_) | Kind::TaggedUnion(_) => {
            Ok(ek.clone())
        }
        other => Err(CompileError::ice(format!(
            "indexing into Vector({other:?}) is not supported"
        ))),
    }
}
