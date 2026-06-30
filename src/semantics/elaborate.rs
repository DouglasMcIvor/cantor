//! AST → SemanticTree elaboration.
//!
//! Resolves the value-position/set-position ambiguity of `+ - * /` (see
//! `tree.rs`) and computes `Kind` for every node, once, bottom-up. Position
//! is determined structurally from *where* an expression appears (a
//! function's domain/range, a `let` constraint, the RHS of `in`, …) — never
//! guessed from the operator alone.
//!
//! **Scope note on value-position Kind.** For most expressions, Kind is a
//! simple structural function of the AST and is computed directly here. But
//! a few cases — `if` with mismatched branch Kinds, `.N`/`[i]` on a
//! `Vector(Tuple(_))`/`Vector(TaggedUnion(_))` base, `++` requiring a
//! tuple-to-vector coercion — are currently *decided* by codegen's own
//! coercion logic (`compile_if`'s tagged-union merging, `compile_proj`'s
//! per-Kind dispatch), entangled with actual LLVM value construction. Rather
//! than re-derive that logic independently here — risking a second
//! implementation that silently disagrees with codegen, exactly the bug
//! class this refactor exists to kill — those cases fail loudly with a
//! clear "not yet implemented in elaborator" error. They become correct once
//! Stage 2 extracts the real decision logic out of codegen.

use std::collections::HashMap;

use crate::ast::{self, BinOp, Expr, ExprKind, FunctionBody, FunctionDef, Item, NameDef, NameDefs, Stmt, UnOp};
use crate::error::CompileError;
use crate::kind::{Kind, set_kind};
use crate::semantics::tree::*;
use crate::span::Symbol;

/// Whether an expression describes a compile-time set (domain/range
/// annotations, `let` constraints, the RHS of `in`, …) or a runtime value
/// (function bodies, `let` values, …) — the one piece of context
/// `BinOp::Add/Sub/Mul/Div` need to resolve to the right `SemExprKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Position {
    Value,
    Set,
}

struct FnSig {
    return_kind: Kind,
}

struct Ctx<'a> {
    name_defs: &'a NameDefs,
    fn_sigs: HashMap<Symbol, FnSig>,
}

type Env = HashMap<Symbol, Kind>;

fn not_yet_implemented(what: &str) -> CompileError {
    CompileError::Internal(format!(
        "not yet implemented in elaborator: {what} — Kind for this case is \
         currently only decided by codegen directly"
    ))
}

/// Elaborate every item in a parsed file into its `SemItem`.
pub fn elaborate(items: &[Item]) -> Result<Vec<SemItem>, CompileError> {
    let name_defs: NameDefs = items.iter()
        .filter_map(|item| match item {
            Item::NameDef(def) => Some((def.name.clone(), def.clone())),
            _ => None,
        })
        .collect();

    // First pass: every function's return Kind, derived from its first
    // signature — mirrors `codegen::Compiler`'s existing rule that
    // overloaded signatures must agree on the Kind of each position.
    // Needed up front so `Call` nodes can resolve a callee's return Kind
    // regardless of declaration order.
    let mut fn_sigs = HashMap::new();
    for item in items {
        if let Item::FunctionDef(def) = item {
            if let Some(sig) = def.sigs.first() {
                fn_sigs.insert(def.name.clone(), FnSig { return_kind: set_kind(&sig.range, &name_defs) });
            }
        }
    }

    let ctx = Ctx { name_defs: &name_defs, fn_sigs };
    items.iter().map(|item| elaborate_item(item, &ctx)).collect()
}

fn function_param_kinds(sig: &ast::FunctionSig, n_params: usize, name_defs: &NameDefs) -> Result<Vec<Kind>, CompileError> {
    if n_params == 0 {
        return Ok(vec![]);
    }
    let parts = ast::param_set_exprs(sig.domain.as_ref(), n_params).map_err(CompileError::Internal)?;
    Ok(parts.into_iter().map(|p| set_kind(p, name_defs)).collect())
}

fn elaborate_item(item: &Item, ctx: &Ctx) -> Result<SemItem, CompileError> {
    match item {
        Item::FunctionDef(def) => elaborate_function_def(def, ctx).map(SemItem::FunctionDef),
        Item::NameDef(def) => elaborate_name_def(def, ctx).map(SemItem::NameDef),
    }
}

fn elaborate_function_def(def: &FunctionDef, ctx: &Ctx) -> Result<SemFunctionDef, CompileError> {
    let sigs = def.sigs.iter()
        .map(|sig| elaborate_sig(sig, def.params.len(), ctx))
        .collect::<Result<Vec<_>, _>>()?;

    let (param_kinds, return_kind) = match sigs.first() {
        Some(s) => (s.param_kinds.clone(), s.return_kind.clone()),
        None => (vec![Kind::Int; def.params.len()], Kind::Int),
    };

    let mut env: Env = def.params.iter()
        .map(|p| p.name.clone())
        .zip(param_kinds.iter().cloned())
        .collect();

    let body = match &def.body {
        FunctionBody::Expr(e) => SemFunctionBody::Expr(elaborate_expr(e, Position::Value, ctx, &mut env)?),
        FunctionBody::Block(stmts) => SemFunctionBody::Block(elaborate_stmts(stmts, ctx, &mut env)?),
    };

    Ok(SemFunctionDef {
        name: def.name.clone(),
        sigs,
        params: def.params.clone(),
        body,
        param_kinds,
        return_kind,
        span: def.span,
    })
}

fn elaborate_sig(sig: &ast::FunctionSig, n_params: usize, ctx: &Ctx) -> Result<SemFunctionSig, CompileError> {
    let mut env = Env::new();
    let domain = sig.domain.as_ref()
        .map(|d| elaborate_expr(d, Position::Set, ctx, &mut env))
        .transpose()?;
    let range = elaborate_expr(&sig.range, Position::Set, ctx, &mut env)?;
    let param_kinds = function_param_kinds(sig, n_params, ctx.name_defs)?;
    let return_kind = set_kind(&sig.range, ctx.name_defs);
    Ok(SemFunctionSig { domain, range, param_kinds, return_kind, span: sig.span })
}

fn elaborate_name_def(def: &NameDef, ctx: &Ctx) -> Result<SemNameDef, CompileError> {
    let mut env = Env::new();
    let ty = def.ty.as_ref().map(|t| elaborate_expr(t, Position::Set, ctx, &mut env)).transpose()?;
    // Annotated form (`name : Set = value`) → value is a runtime value.
    // Unannotated form (`Name = [alias|distinct] value`) → value is itself
    // a set description (the naming convention requires this name be uppercase).
    let value_pos = if def.ty.is_some() { Position::Value } else { Position::Set };
    let value = elaborate_expr(&def.value, value_pos, ctx, &mut env)?;
    Ok(SemNameDef { name: def.name.clone(), kind: def.kind, ty, value, span: def.span })
}

// ── Statements ────────────────────────────────────────────────────────────────

fn elaborate_stmts(stmts: &[Stmt], ctx: &Ctx, env: &mut Env) -> Result<Vec<SemStmt>, CompileError> {
    stmts.iter().map(|s| elaborate_stmt(s, ctx, env)).collect()
}

fn elaborate_stmt(stmt: &Stmt, ctx: &Ctx, env: &mut Env) -> Result<SemStmt, CompileError> {
    Ok(match stmt {
        Stmt::Let { name, constraint, value, span } => {
            let c = elaborate_expr(constraint, Position::Set, ctx, env)?;
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            env.insert(name.clone(), c.kind_of.clone());
            SemStmt::Let { name: name.clone(), constraint: c, value: v, span: *span }
        }
        Stmt::MutLet { name, constraint, value, span } => {
            let c = elaborate_expr(constraint, Position::Set, ctx, env)?;
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            env.insert(name.clone(), c.kind_of.clone());
            SemStmt::MutLet { name: name.clone(), constraint: c, value: v, span: *span }
        }
        Stmt::Assign { name, value, span } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::Assign { name: name.clone(), value: v, span: *span }
        }
        Stmt::DestructLet { bindings, tuple_constraint, value, span } => {
            let (b, tc) = elaborate_destruct_bindings(bindings, tuple_constraint, ctx, env)?;
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::DestructLet { bindings: b, tuple_constraint: tc, value: v, span: *span }
        }
        Stmt::DestructMutLet { bindings, tuple_constraint, value, span } => {
            let (b, tc) = elaborate_destruct_bindings(bindings, tuple_constraint, ctx, env)?;
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::DestructMutLet { bindings: b, tuple_constraint: tc, value: v, span: *span }
        }
        Stmt::DestructAssign { names, value, span } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::DestructAssign { names: names.clone(), value: v, span: *span }
        }
        Stmt::Require { predicate, span } => {
            let p = elaborate_expr(predicate, Position::Value, ctx, env)?;
            SemStmt::Require { predicate: p, span: *span }
        }
        Stmt::Assert { predicate, else_clause, span } => {
            let p = elaborate_expr(predicate, Position::Value, ctx, env)?;
            let ec = else_clause.as_ref().map(|e| elaborate_assert_else(e, ctx, env)).transpose()?;
            SemStmt::Assert { predicate: p, else_clause: ec, span: *span }
        }
        Stmt::Assume { predicate, span } => {
            let p = elaborate_expr(predicate, Position::Value, ctx, env)?;
            SemStmt::Assume { predicate: p, span: *span }
        }
        Stmt::Expr(e) => SemStmt::Expr(elaborate_expr(e, Position::Value, ctx, env)?),
        Stmt::Block(inner) => SemStmt::Block(elaborate_stmts(inner, ctx, env)?),
        Stmt::While { cond, body, span } => {
            let c = elaborate_expr(cond, Position::Value, ctx, env)?;
            let b = elaborate_stmts(body, ctx, env)?;
            SemStmt::While { cond: c, body: b, span: *span }
        }
        Stmt::ForIn { var, set, body, span } => {
            let s = elaborate_expr(set, Position::Set, ctx, env)?;
            let elem_kind = s.kind_of.clone();
            env.insert(var.clone(), elem_kind);
            let b = elaborate_stmts(body, ctx, env)?;
            env.remove(var);
            SemStmt::ForIn { var: var.clone(), set: s, body: b, span: *span }
        }
        Stmt::Return { value, span } => {
            let v = elaborate_expr(value, Position::Value, ctx, env)?;
            SemStmt::Return { value: v, span: *span }
        }
    })
}

fn elaborate_destruct_bindings(
    bindings: &[ast::DestructBinding],
    tuple_constraint: &Option<Expr>,
    ctx: &Ctx,
    env: &mut Env,
) -> Result<(Vec<SemDestructBinding>, Option<SemExpr>), CompileError> {
    let tc = tuple_constraint.as_ref().map(|t| elaborate_expr(t, Position::Set, ctx, env)).transpose()?;
    let sem_bindings = bindings.iter().map(|b| {
        let c = b.constraint.as_ref().map(|c| elaborate_expr(c, Position::Set, ctx, env)).transpose()?;
        if let Some(c) = &c {
            env.insert(b.name.clone(), c.kind_of.clone());
        }
        Ok(SemDestructBinding { name: b.name.clone(), constraint: c })
    }).collect::<Result<Vec<_>, CompileError>>()?;
    Ok((sem_bindings, tc))
}

fn elaborate_assert_else(else_clause: &ast::AssertElse, ctx: &Ctx, env: &mut Env) -> Result<SemAssertElse, CompileError> {
    Ok(match else_clause {
        ast::AssertElse::FailWith(e) => SemAssertElse::FailWith(elaborate_expr(e, Position::Value, ctx, env)?),
        ast::AssertElse::Return(e) => SemAssertElse::Return(elaborate_expr(e, Position::Value, ctx, env)?),
    })
}

// ── Expressions ──────────────────────────────────────────────────────────────

fn elaborate_expr(expr: &Expr, pos: Position, ctx: &Ctx, env: &mut Env) -> Result<SemExpr, CompileError> {
    let span = expr.span;

    // Set-position nodes: `set_kind` already implements every one of these
    // rules correctly (that's its sole purpose) and is exercised by the
    // existing kind_tests/solver/codegen suites, so kind_of is looked up
    // directly from the original AST node instead of re-derived here.
    let kind_of_for_set = || set_kind(expr, ctx.name_defs);

    match &expr.kind {
        ExprKind::IntLit(n) => Ok(SemExpr { kind: SemExprKind::IntLit(*n), kind_of: Kind::Int, span }),
        ExprKind::BoolLit(b) => Ok(SemExpr { kind: SemExprKind::BoolLit(*b), kind_of: Kind::Bool, span }),
        ExprKind::FailLit => Ok(SemExpr {
            kind: SemExprKind::FailLit,
            // Matches codegen::compile_expr exactly: at runtime `fail` is the
            // {i1, i64} fallible-return wrapper, not the bare Fail singleton
            // that `set_kind` uses for set-position membership checks.
            kind_of: Kind::Tuple(vec![Kind::Fail, Kind::Int]),
            span,
        }),

        ExprKind::Var(sym) => {
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                Position::Value => env.get(sym).cloned().ok_or_else(|| CompileError::Internal(
                    format!("elaborate: reference to undefined local `{}`", sym.0)
                ))?,
            };
            Ok(SemExpr { kind: SemExprKind::Var(sym.clone()), kind_of, span })
        }

        ExprKind::BinOp { op: BinOp::Add, lhs, rhs } => {
            let (l, r) = (elaborate_expr(lhs, pos, ctx, env)?, elaborate_expr(rhs, pos, ctx, env)?);
            let (node, kind_of) = match pos {
                Position::Value => (SemExprKind::Add(Box::new(l), Box::new(r)), Kind::Int),
                Position::Set => (SemExprKind::DisjointUnion(Box::new(l), Box::new(r)), kind_of_for_set()),
            };
            Ok(SemExpr { kind: node, kind_of, span })
        }
        ExprKind::BinOp { op: BinOp::Sub, lhs, rhs } => {
            let (l, r) = (elaborate_expr(lhs, pos, ctx, env)?, elaborate_expr(rhs, pos, ctx, env)?);
            let (node, kind_of) = match pos {
                Position::Value => (SemExprKind::Sub(Box::new(l), Box::new(r)), Kind::Int),
                Position::Set => (SemExprKind::SetDifference(Box::new(l), Box::new(r)), kind_of_for_set()),
            };
            Ok(SemExpr { kind: node, kind_of, span })
        }
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs } => {
            let (l, r) = (elaborate_expr(lhs, pos, ctx, env)?, elaborate_expr(rhs, pos, ctx, env)?);
            let (node, kind_of) = match pos {
                Position::Value => (SemExprKind::Mul(Box::new(l), Box::new(r)), Kind::Int),
                Position::Set => (SemExprKind::CartesianProduct(Box::new(l), Box::new(r)), kind_of_for_set()),
            };
            Ok(SemExpr { kind: node, kind_of, span })
        }
        ExprKind::BinOp { op: BinOp::Div, lhs, rhs } => {
            let (l, r) = (elaborate_expr(lhs, pos, ctx, env)?, elaborate_expr(rhs, pos, ctx, env)?);
            let (node, kind_of) = match pos {
                Position::Value => (SemExprKind::Div(Box::new(l), Box::new(r)), Kind::Int),
                Position::Set => (SemExprKind::SetQuotient(Box::new(l), Box::new(r)), kind_of_for_set()),
            };
            Ok(SemExpr { kind: node, kind_of, span })
        }

        // `in`/`not in`: the RHS is always a set description, regardless of
        // the position the `in` expression itself appears in (mirrors
        // compile_membership / membership_constraint, which always treat
        // the RHS as a set expression).
        ExprKind::BinOp { op: op @ (BinOp::In | BinOp::NotIn), lhs, rhs } => {
            let l = elaborate_expr(lhs, Position::Value, ctx, env)?;
            let r = elaborate_expr(rhs, Position::Set, ctx, env)?;
            Ok(SemExpr {
                kind: SemExprKind::BinOp { op: *op, lhs: Box::new(l), rhs: Box::new(r) },
                kind_of: Kind::Bool,
                span,
            })
        }

        ExprKind::BinOp { op: op @ (BinOp::Union | BinOp::Intersect | BinOp::SymDiff), lhs, rhs } => {
            let (l, r) = (elaborate_expr(lhs, pos, ctx, env)?, elaborate_expr(rhs, pos, ctx, env)?);
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                // codegen::compile_binop rejects these outright in value
                // position today ("set operations not yet implemented").
                Position::Value => return Err(not_yet_implemented(&format!("`{op}` in value position"))),
            };
            Ok(SemExpr { kind: SemExprKind::BinOp { op: *op, lhs: Box::new(l), rhs: Box::new(r) }, kind_of, span })
        }

        ExprKind::BinOp { op: BinOp::Concat, lhs, rhs } => {
            let l = elaborate_expr(lhs, Position::Value, ctx, env)?;
            let r = elaborate_expr(rhs, Position::Value, ctx, env)?;
            // Matches compile_vec_concat's clean case: both sides already
            // Vector. Tuple-to-vector coercion is a codegen decision, not
            // yet re-derived here.
            let kind_of = match &l.kind_of {
                Kind::Vector(ek) if matches!(r.kind_of, Kind::Vector(_)) => Kind::Vector(ek.clone()),
                _ => return Err(not_yet_implemented("`++` requiring tuple-to-vector coercion")),
            };
            Ok(SemExpr { kind: SemExprKind::BinOp { op: BinOp::Concat, lhs: Box::new(l), rhs: Box::new(r) }, kind_of, span })
        }

        ExprKind::BinOp { op, lhs, rhs } => {
            // Remaining operators: comparisons and logical and/or — single
            // meaning (Bool) regardless of position.
            let l = elaborate_expr(lhs, pos, ctx, env)?;
            let r = elaborate_expr(rhs, pos, ctx, env)?;
            Ok(SemExpr { kind: SemExprKind::BinOp { op: *op, lhs: Box::new(l), rhs: Box::new(r) }, kind_of: Kind::Bool, span })
        }

        ExprKind::UnOp { op: UnOp::Not, expr: inner } => {
            let e = elaborate_expr(inner, pos, ctx, env)?;
            Ok(SemExpr { kind: SemExprKind::UnOp { op: UnOp::Not, expr: Box::new(e) }, kind_of: Kind::Bool, span })
        }
        ExprKind::UnOp { op: UnOp::Neg, expr: inner } => {
            let e = elaborate_expr(inner, pos, ctx, env)?;
            // Matches set_kind (passes through) in set position and
            // compile_unop (always Int) in value position.
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                Position::Value => Kind::Int,
            };
            Ok(SemExpr { kind: SemExprKind::UnOp { op: UnOp::Neg, expr: Box::new(e) }, kind_of, span })
        }

        ExprKind::Call { callee, args } if callee.0 == "Set" && args.len() == 1 => {
            // Built-in `Set(X)` constructor — its argument is always a set
            // description, regardless of the call's own position.
            let arg = elaborate_expr(&args[0], Position::Set, ctx, env)?;
            Ok(SemExpr { kind: SemExprKind::Call { callee: callee.clone(), args: vec![arg] }, kind_of: kind_of_for_set(), span })
        }
        ExprKind::Call { callee, args } => {
            let sem_args = args.iter().map(|a| elaborate_expr(a, Position::Value, ctx, env)).collect::<Result<Vec<_>, _>>()?;
            let kind_of = ctx.fn_sigs.get(callee)
                .map(|s| s.return_kind.clone())
                .ok_or_else(|| CompileError::Internal(format!("elaborate: call to undeclared function `{}`", callee.0)))?;
            Ok(SemExpr { kind: SemExprKind::Call { callee: callee.clone(), args: sem_args }, kind_of, span })
        }

        ExprKind::If { cond, then_expr, else_expr } => {
            let c = elaborate_expr(cond, Position::Value, ctx, env)?;
            let t = elaborate_expr(then_expr, pos, ctx, env)?;
            let e = elaborate_expr(else_expr, pos, ctx, env)?;
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                Position::Value if t.kind_of == e.kind_of => t.kind_of.clone(),
                // codegen::compile_if merges mismatched branches via tagged-union
                // wrapping/coercion logic not yet re-derived here.
                Position::Value => return Err(not_yet_implemented(&format!(
                    "`if` with mismatched branch kinds (then={:?}, else={:?})", t.kind_of, e.kind_of
                ))),
            };
            Ok(SemExpr { kind: SemExprKind::If { cond: Box::new(c), then_expr: Box::new(t), else_expr: Box::new(e) }, kind_of, span })
        }

        ExprKind::SetLit(elements) => {
            let sem_elements = elements.iter().map(|e| elaborate_expr(e, pos, ctx, env)).collect::<Result<Vec<_>, _>>()?;
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                Position::Value => {
                    // Matches compile_set_lit_value: a non-empty, homogeneous
                    // Int/Bool literal constructs a genuine runtime Set value.
                    let Some(first) = sem_elements.first() else {
                        return Err(CompileError::Internal(
                            "empty set literal in value position — element kind cannot be \
                             inferred; add an explicit annotation".into()
                        ));
                    };
                    let elem_kind = match &first.kind_of {
                        Kind::Int => crate::kind::SetElemKind::Int,
                        Kind::Bool => crate::kind::SetElemKind::Bool,
                        other => return Err(CompileError::Internal(format!(
                            "sets of {other:?} not yet supported"
                        ))),
                    };
                    if sem_elements.iter().any(|e| e.kind_of != first.kind_of) {
                        return Err(CompileError::Internal("mixed element kinds in set literal".into()));
                    }
                    Kind::Set(elem_kind)
                }
            };
            Ok(SemExpr { kind: SemExprKind::SetLit(sem_elements), kind_of, span })
        }

        ExprKind::Try(inner) => {
            let e = elaborate_expr(inner, pos, ctx, env)?;
            // Matches compile_try exactly: always the unwrapped Int payload.
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                Position::Value => Kind::Int,
            };
            Ok(SemExpr { kind: SemExprKind::Try(Box::new(e)), kind_of, span })
        }

        ExprKind::FailWith(inner) => {
            let e = elaborate_expr(inner, Position::Value, ctx, env)?;
            let kind_of = match pos {
                Position::Set => kind_of_for_set(),
                // Matches compile_expr exactly: always the fallible wrapper,
                // regardless of the payload expression's own Kind.
                Position::Value => Kind::Tuple(vec![Kind::Fail, Kind::Int]),
            };
            Ok(SemExpr { kind: SemExprKind::FailWith(Box::new(e)), kind_of, span })
        }

        ExprKind::Comprehension { output, var, source, filter } => {
            if pos == Position::Value {
                // codegen rejects this outright today ("comprehension in
                // value position not yet supported") — comprehensions are
                // set-expression-position only per the v0 design.
                return Err(not_yet_implemented("comprehension in value position"));
            }
            let src = elaborate_expr(source, Position::Set, ctx, env)?;
            env.insert(var.clone(), src.kind_of.clone());
            let out = elaborate_expr(output, Position::Value, ctx, env)?;
            let filt = filter.as_ref().map(|f| elaborate_expr(f, Position::Value, ctx, env)).transpose()?;
            env.remove(var);
            Ok(SemExpr {
                kind: SemExprKind::Comprehension {
                    output: Box::new(out), var: var.clone(), source: Box::new(src), filter: filt.map(Box::new),
                },
                kind_of: kind_of_for_set(),
                span,
            })
        }

        ExprKind::Tuple(elements) => {
            let sem_elements = elements.iter().map(|e| elaborate_expr(e, pos, ctx, env)).collect::<Result<Vec<_>, _>>()?;
            let kind_of = Kind::Tuple(sem_elements.iter().map(|e| e.kind_of.clone()).collect());
            Ok(SemExpr { kind: SemExprKind::Tuple(sem_elements), kind_of, span })
        }

        ExprKind::Proj { base, index } => {
            let b = elaborate_expr(base, pos, ctx, env)?;
            let kind_of = proj_kind(&b.kind_of, *index)?;
            Ok(SemExpr { kind: SemExprKind::Proj { base: Box::new(b), index: *index }, kind_of, span })
        }

        ExprKind::Index { base, index } => {
            let b = elaborate_expr(base, pos, ctx, env)?;
            let i = elaborate_expr(index, Position::Value, ctx, env)?;
            let kind_of = match &b.kind_of {
                Kind::Vector(ek) => vector_elem_kind(ek)?,
                other => return Err(CompileError::Internal(format!("`[i]` requires a vector (X*) base, got {other:?}"))),
            };
            Ok(SemExpr { kind: SemExprKind::Index { base: Box::new(b), index: Box::new(i) }, kind_of, span })
        }

        ExprKind::KleeneStar(inner) => {
            if pos == Position::Value {
                // codegen rejects this outright today ("X* is a set
                // expression and cannot appear in value position").
                return Err(CompileError::Internal("X* is a set expression and cannot appear in value position".into()));
            }
            let e = elaborate_expr(inner, Position::Set, ctx, env)?;
            let kind_of = Kind::Vector(Box::new(e.kind_of.clone()));
            Ok(SemExpr { kind: SemExprKind::KleeneStar(Box::new(e)), kind_of, span })
        }
    }
}

/// `.N` projection's resulting Kind — mirrors `compile_proj`'s simple cases
/// (plain Tuple, TaggedUnion leaves). Vector-of-Tuple/TaggedUnion bases are
/// real codegen capability not yet re-derived here (see module docs).
fn proj_kind(base_kind: &Kind, index: usize) -> Result<Kind, CompileError> {
    match base_kind {
        Kind::Tuple(elems) => elems.get(index).cloned().ok_or_else(|| CompileError::Internal(format!(
            "tuple index {index} out of bounds (tuple has {} elements)", elems.len()
        ))),
        // TaggedUnion's raw LLVM leaves are always plain i64 (Kind::Int).
        Kind::TaggedUnion(_) => Ok(Kind::Int),
        Kind::Vector(ek) => vector_elem_kind(ek),
        other => Err(CompileError::Internal(format!("projection `.{index}` applied to non-tuple value {other:?}"))),
    }
}

/// `Vector(ek)`'s element Kind for `[i]`/`.N` indexing — only the simple
/// cases (`Int`/`Bool`/nested `Vector`) are re-derived here; `Vector(Tuple)`
/// and `Vector(TaggedUnion)` use dedicated codegen dispatch not yet ported.
fn vector_elem_kind(ek: &Kind) -> Result<Kind, CompileError> {
    match ek {
        Kind::Int | Kind::Bool | Kind::Vector(_) => Ok(ek.clone()),
        Kind::Tuple(_) | Kind::TaggedUnion(_) => Err(not_yet_implemented(&format!(
            "indexing into Vector({ek:?}) — requires codegen's struct/union vector dispatch"
        ))),
        other => Err(CompileError::Internal(format!("indexing into Vector({other:?}) is not supported"))),
    }
}
