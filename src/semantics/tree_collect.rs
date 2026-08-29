//! Tree-walking utilities over `SemExpr`/`SemStmt`/`SemFunctionBody` —
//! "find every occurrence of shape X anywhere in this body" queries used by
//! later solver/codegen passes.
//!
//! Split out of `tree.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — same reason
//! `encode_call.rs` was split out of `encode.rs`.

use crate::ast::BinOp;
use crate::span::{Span, Symbol};

use super::tree::{SemAssertElse, SemExpr, SemExprKind, SemFunctionBody, SemStmt};

/// Every `f(args)?` call site in `body`, as `(callee name, ?'s own span)`.
/// Used by `solver::mod`'s propagation-tag check: a `?` on a callee whose
/// range can produce `Fail`/`None` requires the *caller's own* declared
/// range to include that same tag, or codegen would try to `return` a
/// `{tag, i64}` struct from a function declared to return a plain scalar —
/// an LLVM type-mismatch ICE, not a clean diagnostic, if left unchecked (see
/// docs/design-decisions.md §4's "the caller must also declare `Fail`" rule
/// — this function is what actually enforces it).
///
/// Only the `Try(Call { .. })` shape is collected — `?` on any other
/// expression shape isn't a call-narrowing site `encode_call` handles, so it
/// has nothing here to check against. Recurses exhaustively (no wildcard
/// arm) so a future `SemExprKind`/`SemStmt` variant forces an explicit
/// decision here.
pub fn collect_try_calls(body: &SemFunctionBody) -> Vec<(&Symbol, Span)> {
    let mut out = Vec::new();
    match body {
        SemFunctionBody::Expr(e) => collect_try_calls_expr(e, &mut out),
        SemFunctionBody::Block(stmts) => collect_try_calls_stmts(stmts, &mut out),
    }
    out
}

/// `collect_try_calls` for a block body's statement list directly — used by
/// `solver::check_block_sig`, which only has `&[SemStmt]` in hand (not a
/// `SemFunctionBody`, which would require cloning to construct).
pub fn collect_try_calls_stmts<'a>(stmts: &'a [SemStmt], out: &mut Vec<(&'a Symbol, Span)>) {
    stmts.iter().for_each(|s| collect_try_calls_stmt(s, out));
}

fn collect_try_calls_stmt<'a>(stmt: &'a SemStmt, out: &mut Vec<(&'a Symbol, Span)>) {
    match stmt {
        SemStmt::Let {
            constraint, value, ..
        }
        | SemStmt::MutLet {
            constraint, value, ..
        } => {
            collect_try_calls_expr(constraint, out);
            collect_try_calls_expr(value, out);
        }
        SemStmt::Assign { value, .. } | SemStmt::DestructAssign { value, .. } => {
            collect_try_calls_expr(value, out);
        }
        SemStmt::DestructLet {
            tuple_constraint,
            value,
            ..
        }
        | SemStmt::DestructMutLet {
            tuple_constraint,
            value,
            ..
        } => {
            if let Some(c) = tuple_constraint {
                collect_try_calls_expr(c, out);
            }
            collect_try_calls_expr(value, out);
        }
        SemStmt::Require { predicate, .. } | SemStmt::Assume { predicate, .. } => {
            collect_try_calls_expr(predicate, out);
        }
        SemStmt::Assert {
            predicate,
            else_clause,
            ..
        } => {
            collect_try_calls_expr(predicate, out);
            match else_clause {
                None => {}
                Some(SemAssertElse::FailWith(e)) | Some(SemAssertElse::Return(e)) => {
                    collect_try_calls_expr(e, out);
                }
            }
        }
        SemStmt::Expr(e) => collect_try_calls_expr(e, out),
        SemStmt::Block(stmts) => stmts.iter().for_each(|s| collect_try_calls_stmt(s, out)),
        SemStmt::While { cond, body, .. } => {
            collect_try_calls_expr(cond, out);
            body.iter().for_each(|s| collect_try_calls_stmt(s, out));
        }
        SemStmt::ForIn { set, body, .. } => {
            collect_try_calls_expr(set, out);
            body.iter().for_each(|s| collect_try_calls_stmt(s, out));
        }
        SemStmt::Return { value, .. } => collect_try_calls_expr(value, out),
    }
}

pub fn collect_try_calls_expr<'a>(expr: &'a SemExpr, out: &mut Vec<(&'a Symbol, Span)>) {
    match &expr.kind {
        SemExprKind::IntLit(_)
        | SemExprKind::FloatLit(_)
        | SemExprKind::BoolLit(_)
        | SemExprKind::CharLit(_)
        | SemExprKind::Var(_)
        | SemExprKind::FailLit
        | SemExprKind::NoneLit => {}
        SemExprKind::Add(l, r)
        | SemExprKind::DisjointUnion(l, r)
        | SemExprKind::Sub(l, r)
        | SemExprKind::SetDifference(l, r)
        | SemExprKind::Mul(l, r)
        | SemExprKind::CartesianProduct(l, r)
        | SemExprKind::Div(l, r) => {
            collect_try_calls_expr(l, out);
            collect_try_calls_expr(r, out);
        }
        SemExprKind::SetQuotient(l, _canon) => collect_try_calls_expr(l, out),
        SemExprKind::BinOp { lhs, rhs, .. } => {
            collect_try_calls_expr(lhs, out);
            collect_try_calls_expr(rhs, out);
        }
        SemExprKind::UnOp { expr, .. } => collect_try_calls_expr(expr, out),
        SemExprKind::Call { args, .. } => args.iter().for_each(|a| collect_try_calls_expr(a, out)),
        SemExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_try_calls_expr(cond, out);
            collect_try_calls_expr(then_expr, out);
            collect_try_calls_expr(else_expr, out);
        }
        SemExprKind::SetLit(exprs) | SemExprKind::Tuple(exprs) => {
            exprs.iter().for_each(|e| collect_try_calls_expr(e, out));
        }
        SemExprKind::Try(inner) => {
            if let SemExprKind::Call { callee, args } = &inner.kind {
                out.push((callee, expr.span));
                args.iter().for_each(|a| collect_try_calls_expr(a, out));
            } else {
                collect_try_calls_expr(inner, out);
            }
        }
        SemExprKind::FailWith(e) | SemExprKind::KleeneStar(e) => collect_try_calls_expr(e, out),
        SemExprKind::Comprehension {
            output,
            source,
            filter,
            ..
        } => {
            collect_try_calls_expr(output, out);
            collect_try_calls_expr(source, out);
            if let Some(f) = filter {
                collect_try_calls_expr(f, out);
            }
        }
        SemExprKind::Proj { base, .. } => collect_try_calls_expr(base, out),
        SemExprKind::Index { base, index } => {
            collect_try_calls_expr(base, out);
            collect_try_calls_expr(index, out);
        }
    }
}

/// Every `f >> g` (function composition, higher-order functions v0) node
/// anywhere in `body`, in some (unspecified) order — codegen's
/// `expr_call::ensure_compose_wrapper` pre-builds each one's standalone
/// wrapper function before body compilation proper begins (mirrors
/// `collect_try_calls`'s "collect first, act after" shape, and reuses this
/// walk's exhaustive-recursion discipline for the same reason: a future
/// `SemExprKind`/`SemStmt` variant should force an explicit decision here,
/// not silently skip composition nodes nested inside it).
pub fn collect_compose_nodes(body: &SemFunctionBody) -> Vec<&SemExpr> {
    let mut out = Vec::new();
    match body {
        SemFunctionBody::Expr(e) => collect_compose_nodes_expr(e, &mut out),
        SemFunctionBody::Block(stmts) => collect_compose_nodes_stmts(stmts, &mut out),
    }
    out
}

pub fn collect_compose_nodes_stmts<'a>(stmts: &'a [SemStmt], out: &mut Vec<&'a SemExpr>) {
    stmts
        .iter()
        .for_each(|s| collect_compose_nodes_stmt(s, out));
}

fn collect_compose_nodes_stmt<'a>(stmt: &'a SemStmt, out: &mut Vec<&'a SemExpr>) {
    match stmt {
        SemStmt::Let {
            constraint, value, ..
        }
        | SemStmt::MutLet {
            constraint, value, ..
        } => {
            collect_compose_nodes_expr(constraint, out);
            collect_compose_nodes_expr(value, out);
        }
        SemStmt::Assign { value, .. } | SemStmt::DestructAssign { value, .. } => {
            collect_compose_nodes_expr(value, out);
        }
        SemStmt::DestructLet {
            tuple_constraint,
            value,
            ..
        }
        | SemStmt::DestructMutLet {
            tuple_constraint,
            value,
            ..
        } => {
            if let Some(c) = tuple_constraint {
                collect_compose_nodes_expr(c, out);
            }
            collect_compose_nodes_expr(value, out);
        }
        SemStmt::Require { predicate, .. } | SemStmt::Assume { predicate, .. } => {
            collect_compose_nodes_expr(predicate, out);
        }
        SemStmt::Assert {
            predicate,
            else_clause,
            ..
        } => {
            collect_compose_nodes_expr(predicate, out);
            match else_clause {
                None => {}
                Some(SemAssertElse::FailWith(e)) | Some(SemAssertElse::Return(e)) => {
                    collect_compose_nodes_expr(e, out);
                }
            }
        }
        SemStmt::Expr(e) => collect_compose_nodes_expr(e, out),
        SemStmt::Block(stmts) => stmts
            .iter()
            .for_each(|s| collect_compose_nodes_stmt(s, out)),
        SemStmt::While { cond, body, .. } => {
            collect_compose_nodes_expr(cond, out);
            body.iter().for_each(|s| collect_compose_nodes_stmt(s, out));
        }
        SemStmt::ForIn { set, body, .. } => {
            collect_compose_nodes_expr(set, out);
            body.iter().for_each(|s| collect_compose_nodes_stmt(s, out));
        }
        SemStmt::Return { value, .. } => collect_compose_nodes_expr(value, out),
    }
}

fn collect_compose_nodes_expr<'a>(expr: &'a SemExpr, out: &mut Vec<&'a SemExpr>) {
    if matches!(
        &expr.kind,
        SemExprKind::BinOp {
            op: BinOp::Compose,
            ..
        }
    ) {
        out.push(expr);
        // Deliberately does not recurse into a Compose node's own lhs/rhs:
        // elaboration restricts both to a bare function reference or
        // another Compose node (never an arbitrary expression that could
        // itself contain further nested calls/composes to find) — see
        // `semantics::elaborate::binop`'s `Compose` arm.
        return;
    }
    match &expr.kind {
        SemExprKind::IntLit(_)
        | SemExprKind::FloatLit(_)
        | SemExprKind::BoolLit(_)
        | SemExprKind::CharLit(_)
        | SemExprKind::Var(_)
        | SemExprKind::FailLit
        | SemExprKind::NoneLit => {}
        SemExprKind::Add(l, r)
        | SemExprKind::DisjointUnion(l, r)
        | SemExprKind::Sub(l, r)
        | SemExprKind::SetDifference(l, r)
        | SemExprKind::Mul(l, r)
        | SemExprKind::CartesianProduct(l, r)
        | SemExprKind::Div(l, r) => {
            collect_compose_nodes_expr(l, out);
            collect_compose_nodes_expr(r, out);
        }
        SemExprKind::SetQuotient(l, _canon) => collect_compose_nodes_expr(l, out),
        SemExprKind::BinOp { lhs, rhs, .. } => {
            collect_compose_nodes_expr(lhs, out);
            collect_compose_nodes_expr(rhs, out);
        }
        SemExprKind::UnOp { expr, .. } => collect_compose_nodes_expr(expr, out),
        SemExprKind::Call { args, .. } => {
            args.iter().for_each(|a| collect_compose_nodes_expr(a, out));
        }
        SemExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_compose_nodes_expr(cond, out);
            collect_compose_nodes_expr(then_expr, out);
            collect_compose_nodes_expr(else_expr, out);
        }
        SemExprKind::SetLit(exprs) | SemExprKind::Tuple(exprs) => {
            exprs
                .iter()
                .for_each(|e| collect_compose_nodes_expr(e, out));
        }
        SemExprKind::Try(inner) => collect_compose_nodes_expr(inner, out),
        SemExprKind::FailWith(e) | SemExprKind::KleeneStar(e) => collect_compose_nodes_expr(e, out),
        SemExprKind::Comprehension {
            output,
            source,
            filter,
            ..
        } => {
            collect_compose_nodes_expr(output, out);
            collect_compose_nodes_expr(source, out);
            if let Some(f) = filter {
                collect_compose_nodes_expr(f, out);
            }
        }
        SemExprKind::Proj { base, .. } => collect_compose_nodes_expr(base, out),
        SemExprKind::Index { base, index } => {
            collect_compose_nodes_expr(base, out);
            collect_compose_nodes_expr(index, out);
        }
    }
}
