//! AST → SemanticTree elaboration.
//!
//! Resolves the value-position/set-position ambiguity of `+ - * /` (see
//! `tree.rs`) and computes `Kind` for every node, once, bottom-up. Position
//! is determined structurally from *where* an expression appears (a
//! function's domain/range, a `let` constraint, the RHS of `in`, …) — never
//! guessed from the operator alone.
//!
//! **Value-position Kind for `if`/`++`/vector indexing** used to be decided
//! only by codegen's own coercion logic, entangled with actual LLVM value
//! construction — re-deriving it independently here risked a second
//! implementation that silently disagreed with codegen, exactly the bug
//! class this refactor exists to kill. `kind::merge_if_branches` and
//! `kind::merge_concat_kinds` now extract that decision (the resulting Kind
//! and which coercion applies) into pure functions that both codegen and
//! this module call, so the two cannot drift apart. `.N`/`[i]` on a
//! `Vector(Tuple(_))`/`Vector(TaggedUnion(_))` base needed no extraction:
//! indexing into either always yields the element Kind unchanged (see
//! `vector_elem_kind`).

mod binop;

use std::collections::HashMap;

use crate::ast::{
    self, DefKind, Expr, ExprKind, FunctionBody, FunctionDef, Item, NameDef, NameDefs, Stmt, UnOp,
};
use crate::error::CompileError;
use crate::kind::{Kind, set_kind};
use crate::semantics::tree::*;
use crate::span::{Span, Symbol};

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

fn not_yet_implemented(what: &str, span: Span) -> CompileError {
    CompileError::Unsupported {
        feature: what.to_string(),
        span,
    }
}

/// Elaborate every item in a parsed file into its `SemItem`.
pub fn elaborate(items: &[Item]) -> Result<Vec<SemItem>, CompileError> {
    let name_defs: NameDefs = items
        .iter()
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
        if let Item::FunctionDef(def) = item
            && let Some(sig) = def.sigs.first()
        {
            fn_sigs.insert(
                def.name.clone(),
                FnSig {
                    return_kind: crate::kind::range_kind(&sig.range, &name_defs)?,
                },
            );
        }
    }

    let ctx = Ctx {
        name_defs: &name_defs,
        fn_sigs,
    };
    let sem_items: Vec<SemItem> = items
        .iter()
        .map(|item| elaborate_item(item, &ctx))
        .collect::<Result<_, _>>()?;
    check_overload_kind_agreement(&sem_items)?;
    Ok(sem_items)
}

/// int-soundness-plan phase 2: multiple `FunctionDef`s may share a name,
/// forming an overload set — but only across definitions of the *same*
/// arity (differing arity is itself a free, always-static dispatch key, so
/// there's nothing to agree on there). Within a same-name-same-arity group,
/// every member must still agree on the Kind of each parameter position and
/// on the return Kind, exactly as today's multiple-signatures-one-body
/// feature already requires within a single `FunctionDef`.
///
/// int-soundness-plan phase 3 (step 2): one narrow, structural exception —
/// a position may disagree between `Kind::Int` and `Kind::Int64` when
/// *both* overloads are marked `compiler_generated_split`
/// (`kinds_agree_for_split`). This is not a general relaxation: nothing
/// produces `compiler_generated_split = true` yet (step 4 will, generating
/// exactly this `Int64`/`BigInt` pair from one unbounded-`Int` signature —
/// see design-decisions.md §7 and int-soundness-plan.md's "Phase 3"
/// section), so every mismatch reaching this function today still errors
/// exactly as it did before this exception existed.
pub fn check_overload_kind_agreement(sem_items: &[SemItem]) -> Result<(), CompileError> {
    let mut groups: HashMap<(Symbol, usize), Vec<&SemFunctionDef>> = HashMap::new();
    for item in sem_items {
        if let SemItem::FunctionDef(def) = item {
            groups
                .entry((def.name.clone(), def.params.len()))
                .or_default()
                .push(def);
        }
    }
    for defs in groups.values() {
        let Some((first, rest)) = defs.split_first() else {
            continue;
        };
        for other in rest {
            let mismatched =
                other.return_kind != first.return_kind || other.param_kinds != first.param_kinds;
            if !mismatched {
                continue;
            }
            if first.compiler_generated_split
                && other.compiler_generated_split
                && kinds_agree_for_split(&first.return_kind, &other.return_kind)
                && first.param_kinds.len() == other.param_kinds.len()
                && first
                    .param_kinds
                    .iter()
                    .zip(&other.param_kinds)
                    .all(|(a, b)| kinds_agree_for_split(a, b))
            {
                continue;
            }
            return Err(CompileError::OverloadKindMismatch {
                name: other.name.0.clone(),
                detail: format!(
                    "an earlier overload has param kinds {:?} and return kind {:?}, \
                     but this one has {:?} and {:?}",
                    first.param_kinds, first.return_kind, other.param_kinds, other.return_kind
                ),
                span: other.span,
            });
        }
    }
    Ok(())
}

/// True when `a` and `b` are the same Kind, or are exactly the one pairing
/// int-soundness-plan phase 3 needs at a single position: `Kind::Int`
/// (tagged/general) paired with `Kind::Int64` (raw), order-independent.
/// Never true for any other pair of differing Kinds — this is the full
/// extent of the exception `check_overload_kind_agreement` grants compiler-
/// generated overload pairs; every other mismatch still errors.
fn kinds_agree_for_split(a: &Kind, b: &Kind) -> bool {
    a == b || matches!((a, b), (Kind::Int, Kind::Int64) | (Kind::Int64, Kind::Int))
}

/// `codegen::compile_call`'s built-in identity/cardinality calls — never
/// user-declared, so absent from `fn_sigs`. All four always return `Kind::Int`.
fn builtin_call_kind(callee: &Symbol, args_len: usize, name_defs: &NameDefs) -> Option<Kind> {
    if args_len != 1 {
        return None;
    }
    if callee.0 == "from" || callee.0 == "size" || callee.0 == "len" {
        return Some(Kind::Int);
    }
    // Auto-generated constructor `d(x)` for `D = distinct B`.
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    match name_defs.get(&Symbol(capitalized)) {
        Some(def) if def.kind == DefKind::Distinct => Some(Kind::Int),
        _ => None,
    }
}

fn function_param_kinds(
    sig: &ast::FunctionSig,
    n_params: usize,
    name_defs: &NameDefs,
) -> Result<Vec<Kind>, CompileError> {
    if n_params == 0 {
        return Ok(vec![]);
    }
    let parts =
        ast::param_set_exprs(sig.domain.as_ref(), n_params).map_err(|e| CompileError::ice(e))?;
    parts.into_iter().map(|p| set_kind(p, name_defs)).collect()
}

fn elaborate_item(item: &Item, ctx: &Ctx) -> Result<SemItem, CompileError> {
    match item {
        Item::FunctionDef(def) => elaborate_function_def(def, ctx).map(SemItem::FunctionDef),
        Item::NameDef(def) => elaborate_name_def(def, ctx).map(SemItem::NameDef),
    }
}

fn elaborate_function_def(def: &FunctionDef, ctx: &Ctx) -> Result<SemFunctionDef, CompileError> {
    let sigs = def
        .sigs
        .iter()
        .map(|sig| elaborate_sig(sig, def.params.len(), ctx))
        .collect::<Result<Vec<_>, _>>()?;

    let (param_kinds, return_kind) = match sigs.first() {
        Some(s) => (s.param_kinds.clone(), s.return_kind.clone()),
        None => (vec![Kind::Int; def.params.len()], Kind::Int),
    };

    let mut env: Env = def
        .params
        .iter()
        .map(|p| p.name.clone())
        .zip(param_kinds.iter().cloned())
        .collect();

    let body = match &def.body {
        FunctionBody::Expr(e) => {
            SemFunctionBody::Expr(elaborate_expr(e, Position::Value, ctx, &mut env)?)
        }
        FunctionBody::Block(stmts) => {
            SemFunctionBody::Block(elaborate_stmts(stmts, ctx, &mut env)?)
        }
    };

    Ok(SemFunctionDef {
        name: def.name.clone(),
        sigs,
        params: def.params.clone(),
        body,
        param_kinds,
        return_kind,
        span: def.span,
        // Only the (not-yet-implemented) phase 3 split generator sets this.
        compiler_generated_split: false,
    })
}

fn elaborate_sig(
    sig: &ast::FunctionSig,
    n_params: usize,
    ctx: &Ctx,
) -> Result<SemFunctionSig, CompileError> {
    let mut env = Env::new();
    let domain = sig
        .domain
        .as_ref()
        .map(|d| elaborate_expr(d, Position::Set, ctx, &mut env))
        .transpose()?;
    let range = elaborate_expr(&sig.range, Position::Set, ctx, &mut env)?;
    let param_kinds = function_param_kinds(sig, n_params, ctx.name_defs)?;
    let return_kind = crate::kind::range_kind(&sig.range, ctx.name_defs)?;
    Ok(SemFunctionSig {
        domain,
        range,
        param_kinds,
        return_kind,
        span: sig.span,
    })
}

fn elaborate_name_def(def: &NameDef, ctx: &Ctx) -> Result<SemNameDef, CompileError> {
    let mut env = Env::new();
    let ty = def
        .ty
        .as_ref()
        .map(|t| elaborate_expr(t, Position::Set, ctx, &mut env))
        .transpose()?;
    // Annotated form (`name : Set = value`) → value is a runtime value.
    // Unannotated form (`Name = [alias|distinct] value`) → value is itself
    // a set description (the naming convention requires this name be uppercase).
    let value_pos = if def.ty.is_some() {
        Position::Value
    } else {
        Position::Set
    };
    let value = elaborate_expr(&def.value, value_pos, ctx, &mut env)?;
    Ok(SemNameDef {
        name: def.name.clone(),
        kind: def.kind,
        ty,
        value,
        span: def.span,
    })
}

// ── Statements ────────────────────────────────────────────────────────────────

fn elaborate_stmts(stmts: &[Stmt], ctx: &Ctx, env: &mut Env) -> Result<Vec<SemStmt>, CompileError> {
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

// ── Expressions ──────────────────────────────────────────────────────────────

fn elaborate_expr(
    expr: &Expr,
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

        ExprKind::BinOp { op, lhs, rhs } => binop::elaborate_binop(
            binop::BinOpNode {
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
            // Matches set_kind (passes through) in set position and
            // compile_unop (always Int) in value position.
            let kind_of = match pos {
                Position::Set => kind_of_for_set()?,
                Position::Value => Kind::Int,
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
            let kind_of = match &b.kind_of {
                Kind::Vector(ek) => vector_elem_kind(ek)?,
                other => {
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
        // TaggedUnion's raw LLVM leaves are always plain i64 (Kind::Int).
        Kind::TaggedUnion(_) => Ok(Kind::Int),
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
