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
mod expr;
mod stmt;

use std::collections::HashMap;

use crate::ast::{self, DefKind, FunctionBody, FunctionDef, Item, NameDef, NameDefs};
use crate::error::CompileError;
use crate::kind::{Kind, set_kind};
use crate::semantics::tree::*;
use crate::span::{Span, Symbol};

use expr::elaborate_expr;
use stmt::elaborate_stmts;

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
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    // Auto-generated constructor for a wrapping fixed-width integer builtin
    // (`signed32(n)`/`unsigned32(n)`, docs/wrapping-and-quotient-sets-
    // plan.md): unlike `distinct`, a wrapping sort genuinely gets its own
    // runtime Kind (different LLVM width/ABI extension), so this must be
    // checked *before* falling through to the `distinct`-only default below.
    match crate::semantics::builtins::lookup(&capitalized) {
        Some(b) if b.kind == Kind::Signed32 || b.kind == Kind::Unsigned32 => Some(b.kind),
        _ => {
            // Auto-generated constructor `d(x)` for `D = distinct B`.
            //
            // TODO: hardcoding `Kind::Int` here is a holdover from when
            // `distinct` could only wrap an Int-sorted basis set (a rapid-
            // prototyping-era assumption, not a deliberate design choice).
            // `distinct` should eventually generalise to wrap *any* basis
            // set/Kind — at that point this needs to return the
            // constructor's actual result Kind (derived from the basis, not
            // unconditionally `Int`).
            match name_defs.get(&Symbol(capitalized)) {
                Some(def) if def.kind == DefKind::Distinct => Some(Kind::Int),
                _ => None,
            }
        }
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
