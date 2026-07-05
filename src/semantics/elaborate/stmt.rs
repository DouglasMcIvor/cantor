//! Elaboration of statements: `let`/`mut let`, assignment, destructuring,
//! `require`/`assert`/`assume`, blocks, `while`/`for`, and `return`.

use crate::ast::{self, Expr, ExprKind, Stmt};
use crate::error::CompileError;
use crate::kind::Kind;
use crate::semantics::tree::*;

use super::{Ctx, Env, Position, elaborate_expr};

pub(super) fn elaborate_stmts(
    stmts: &[Stmt],
    ctx: &Ctx,
    env: &mut Env,
) -> Result<Vec<SemStmt>, CompileError> {
    stmts.iter().map(|s| elaborate_stmt(s, ctx, env)).collect()
}

fn elaborate_stmt(stmt: &Stmt, ctx: &Ctx, env: &mut Env) -> Result<SemStmt, CompileError> {
    Ok(match stmt {
        Stmt::Let {
            name,
            constraint,
            value,
            span,
        } => {
            let c = elaborate_expr(constraint, Position::Set, ctx, env)?;
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            env.insert(name.clone(), c.kind_of.clone());
            SemStmt::Let {
                name: name.clone(),
                constraint: c,
                value: v,
                span: *span,
            }
        }
        Stmt::MutLet {
            name,
            constraint,
            value,
            span,
        } => {
            let c = elaborate_expr(constraint, Position::Set, ctx, env)?;
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            env.insert(name.clone(), c.kind_of.clone());
            SemStmt::MutLet {
                name: name.clone(),
                constraint: c,
                value: v,
                span: *span,
            }
        }
        Stmt::Assign { name, value, span } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::Assign {
                name: name.clone(),
                value: v,
                span: *span,
            }
        }
        Stmt::DestructLet {
            bindings,
            tuple_constraint,
            value,
            span,
        } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            let (b, tc) =
                elaborate_destruct_bindings(bindings, tuple_constraint, &v.kind_of, ctx, env)?;
            SemStmt::DestructLet {
                bindings: b,
                tuple_constraint: tc,
                value: v,
                span: *span,
            }
        }
        Stmt::DestructMutLet {
            bindings,
            tuple_constraint,
            value,
            span,
        } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            let (b, tc) =
                elaborate_destruct_bindings(bindings, tuple_constraint, &v.kind_of, ctx, env)?;
            SemStmt::DestructMutLet {
                bindings: b,
                tuple_constraint: tc,
                value: v,
                span: *span,
            }
        }
        Stmt::DestructAssign { names, value, span } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::DestructAssign {
                names: names.clone(),
                value: v,
                span: *span,
            }
        }
        Stmt::Require { predicate, span } => {
            let p = elaborate_expr(predicate, Position::Value, ctx, env)?;
            SemStmt::Require {
                predicate: p,
                span: *span,
            }
        }
        Stmt::Assert {
            predicate,
            else_clause,
            span,
        } => {
            let p = elaborate_expr(predicate, Position::Value, ctx, env)?;
            let ec = else_clause
                .as_ref()
                .map(|e| elaborate_assert_else(e, ctx, env))
                .transpose()?;
            SemStmt::Assert {
                predicate: p,
                else_clause: ec,
                span: *span,
            }
        }
        Stmt::Assume { predicate, span } => {
            let p = elaborate_expr(predicate, Position::Value, ctx, env)?;
            SemStmt::Assume {
                predicate: p,
                span: *span,
            }
        }
        Stmt::Expr(e) => SemStmt::Expr(elaborate_expr(e, Position::Value, ctx, env)?),
        Stmt::Block(inner) => SemStmt::Block(elaborate_stmts(inner, ctx, env)?),
        Stmt::While { cond, body, span } => {
            let c = elaborate_expr(cond, Position::Value, ctx, env)?;
            let b = elaborate_stmts(body, ctx, env)?;
            SemStmt::While {
                cond: c,
                body: b,
                span: *span,
            }
        }
        Stmt::ForIn {
            var,
            set,
            body,
            span,
        } => {
            // Unlike domain/range/`let`-constraint positions, `for`'s iterable
            // is never a compile-time set *description* except when it's a
            // comprehension (which `codegen::compile_for_in` unrolls specially
            // and which elaborate_expr already restricts to Position::Set).
            // A set literal `{1, 2, 3}` is unrolled element-by-element, each
            // element compiled as an ordinary value expression (e.g. `n + 1`
            // must stay arithmetic, not become a disjoint union); a bare
            // variable is a runtime `Kind::Set(_)` value looked up like any
            // other local. Both need Position::Value.
            let is_comprehension = matches!(set.kind, ExprKind::Comprehension { .. });
            let is_empty_set_lit =
                matches!(&set.kind, ExprKind::SetLit(elements) if elements.is_empty());
            let s = if is_empty_set_lit {
                // Element Kind is unknowable from zero elements — but
                // harmless: `codegen::compile_for_in` unrolls a SetLit
                // iterable at compile time, so an empty literal produces
                // zero copies of the body regardless of what Kind `var`
                // gets bound to here. (The generic value-position SetLit
                // rule below requires a nonempty literal to infer one.)
                SemExpr {
                    kind: SemExprKind::SetLit(vec![]),
                    kind_of: Kind::Int,
                    span: set.span,
                }
            } else {
                elaborate_expr(
                    set,
                    if is_comprehension {
                        Position::Set
                    } else {
                        Position::Value
                    },
                    ctx,
                    env,
                )?
            };
            let elem_kind = match &s.kind_of {
                Kind::Set(inner) => (**inner).clone(),
                other => other.clone(),
            };
            env.insert(var.clone(), elem_kind);
            let b = elaborate_stmts(body, ctx, env)?;
            env.remove(var);
            SemStmt::ForIn {
                var: var.clone(),
                set: s,
                body: b,
                span: *span,
            }
        }
        Stmt::Return { value, span } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::Return {
                value: v,
                span: *span,
            }
        }
    })
}

/// Elaborate a destructuring's per-binding constraints and bind each name to
/// its Kind in `env`. A binding's Kind always comes from `value_kind` (the
/// already-elaborated RHS's Tuple element Kinds) — mirrors
/// `codegen::blocks`'s `DestructLet` handling exactly, which derives Kind
/// purely from the RHS tuple and never consults the constraint annotations
/// (those are solver-only proof obligations, not a second source of Kind).
/// Using the constraint's Kind instead would leave *unconstrained* bindings
/// (`x, y = (p.0, p.1)`, no `: Type` annotations) with no Kind in `env` at all.
fn elaborate_destruct_bindings(
    bindings: &[ast::DestructBinding],
    tuple_constraint: &Option<Expr>,
    value_kind: &Kind,
    ctx: &Ctx,
    env: &mut Env,
) -> Result<(Vec<SemDestructBinding>, Option<SemExpr>), CompileError> {
    let tc = tuple_constraint
        .as_ref()
        .map(|t| elaborate_expr(t, Position::Set, ctx, env))
        .transpose()?;
    let elem_kinds = match value_kind {
        Kind::Tuple(ek) => ek,
        // The README documents `h, t = v` for a vector `v` (head elements plus
        // a vector tail, proof-gated on `v` having enough elements) — that is
        // not yet implemented in any of elaborate/solver/codegen. Reported as
        // an explicit not-yet-implemented error rather than a generic
        // "wrong shape" one, since it's a real (if unimplemented) construct,
        // not a type error.
        Kind::Vector(_) => {
            return Err(CompileError::ice(
                "not yet implemented: destructuring a vector (`X*`) — only tuple \
             right-hand sides are currently supported",
            ));
        }
        other => {
            return Err(CompileError::ice(format!(
                "destructuring requires a tuple on the right-hand side, got {other:?}"
            )));
        }
    };
    if bindings.len() > elem_kinds.len() {
        return Err(CompileError::ice(format!(
            "destructuring arity mismatch: {} binding(s) but tuple has only {} element(s)",
            bindings.len(),
            elem_kinds.len()
        )));
    }
    let last_i = bindings.len() - 1;
    let sem_bindings = bindings
        .iter()
        .enumerate()
        .map(|(i, b)| {
            let c = b
                .constraint
                .as_ref()
                .map(|c| elaborate_expr(c, Position::Set, ctx, env))
                .transpose()?;
            let tail_count = elem_kinds.len() - i;
            // The last binder receives the remaining elements as a sub-tuple
            // when there are more tuple elements than bindings.
            let binding_kind = if i < last_i || tail_count == 1 {
                elem_kinds[i].clone()
            } else {
                Kind::Tuple(elem_kinds[i..].to_vec())
            };
            env.insert(b.name.clone(), binding_kind);
            Ok(SemDestructBinding {
                name: b.name.clone(),
                constraint: c,
            })
        })
        .collect::<Result<Vec<_>, CompileError>>()?;
    Ok((sem_bindings, tc))
}

fn elaborate_assert_else(
    else_clause: &ast::AssertElse,
    ctx: &Ctx,
    env: &mut Env,
) -> Result<SemAssertElse, CompileError> {
    Ok(match else_clause {
        ast::AssertElse::FailWith(e) => {
            SemAssertElse::FailWith(elaborate_expr(e, Position::Value, ctx, env)?)
        }
        ast::AssertElse::Return(e) => {
            SemAssertElse::Return(elaborate_expr(e, Position::Value, ctx, env)?)
        }
    })
}
