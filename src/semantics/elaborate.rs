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

/// One `FunctionDef`'s Kind signature, keyed by name in `Ctx::fn_sigs` —
/// there may be several per name (arity- and/or param-Kind-bucket-
/// distinguished overloads), so `Call` elaboration (`expr.rs`) matches a
/// call's already-elaborated argument Kinds against `param_kinds` here to
/// pick the right one's `return_kind`, rather than assuming one signature
/// per name (see `check_overload_kind_agreement`'s doc comment for why
/// matching on Kind alone is always unambiguous).
struct FnSig {
    param_kinds: Vec<Kind>,
    return_kind: Kind,
}

struct Ctx<'a> {
    name_defs: &'a NameDefs,
    fn_sigs: HashMap<Symbol, Vec<FnSig>>,
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

    super::wellfounded::check_well_founded(items, &name_defs)?;

    // First pass: every function's parameter Kinds and return Kind, derived
    // from its first signature — mirrors `codegen::Compiler`'s existing rule
    // that overloaded signatures must agree on the Kind of each position
    // *within* a parameter-Kind bucket (`check_overload_kind_agreement`).
    // Needed up front so `Call` nodes can resolve a callee's return Kind
    // regardless of declaration order. One `Vec` entry per `FunctionDef` of
    // this name (not deduplicated by bucket) — `Call` elaboration below
    // matches the call's own argument Kinds against `param_kinds` to pick
    // the right entry, so a same-name/different-arity or same-name/
    // different-Kind-bucket overload never sees another's return Kind.
    let mut fn_sigs: HashMap<Symbol, Vec<FnSig>> = HashMap::new();
    for item in items {
        if let Item::FunctionDef(def) = item
            && let Some(sig) = def.sigs.first()
        {
            let param_kinds = function_param_kinds(sig, def.params.len(), &name_defs)?;
            fn_sigs.entry(def.name.clone()).or_default().push(FnSig {
                param_kinds,
                return_kind: crate::kind::range_kind(&sig.range, &name_defs)?,
            });
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

/// int-soundness-plan phase 2 / backlog.md "function overloads — support
/// different kinds": multiple `FunctionDef`s may share a name, forming an
/// overload set — but only across definitions of the *same* arity (differing
/// arity is itself a free, always-static dispatch key, so there's nothing to
/// agree on there). Within a same-name-same-arity group, members are further
/// partitioned into Kind buckets (`bucket_key`, one per distinct parameter-
/// Kind tuple, modulo the `Int`/`Int64` split identification below): every
/// member of one bucket must still agree exactly on the Kind of each
/// parameter position and on the return Kind, exactly as today's multiple-
/// signatures-one-body feature already requires within a single
/// `FunctionDef`. Different buckets need no relation to each other at all —
/// a `Bool` value and an `Int` value can never be equal, so two overloads
/// whose Kind signatures genuinely differ are automatically disjoint (see
/// design-decisions.md §7/§12: this works because `Kind` is always
/// statically known per call-site argument in this language, so resolving
/// *which* bucket a call belongs to never needs a runtime/solver decision —
/// unlike resolving *within* a bucket, where two overloads can share a Kind
/// but still need a domain-disjointness proof).
///
/// int-soundness-plan phase 3 (step 2): one narrow, structural exception —
/// a position may disagree between `Kind::Int` and `Kind::Int64` when
/// *both* overloads are marked `compiler_generated_split`
/// (`kinds_agree_for_split`). This is not a general relaxation: nothing
/// produces `compiler_generated_split = true` yet (step 4 will, generating
/// exactly this `Int64`/`BigInt` pair from one unbounded-`Int` signature —
/// see design-decisions.md §7 and int-soundness-plan.md's "Phase 3"
/// section). `bucket_key` folds `Int64` into `Int` for exactly this reason:
/// the split's two overloads must land in the *same* bucket (so the
/// existing Int64/BigInt disjointness+dispatch machinery still applies to
/// them), while an unrelated `Bool` overload of the same name/arity lands in
/// a genuinely separate bucket.
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
        // Partition `defs` into Kind buckets — linear scan (not a HashMap)
        // since `Kind` has no `Hash` impl and overload sets are always small.
        let mut buckets: Vec<Vec<&SemFunctionDef>> = Vec::new();
        for def in defs {
            match buckets
                .iter_mut()
                .find(|bucket| bucket_key(bucket[0]) == bucket_key(def))
            {
                Some(bucket) => bucket.push(def),
                None => buckets.push(vec![def]),
            }
        }
        for bucket in &buckets {
            let Some((first, rest)) = bucket.split_first() else {
                continue;
            };
            for other in rest {
                let mismatched = other.return_kind != first.return_kind
                    || other.param_kinds != first.param_kinds;
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

/// Folds `Kind::Int64` to `Kind::Int` (the only identification
/// `check_overload_kind_agreement`'s buckets make — see that function's doc
/// comment) so the phase 3 `Int64`/`BigInt` split's two overloads land in one
/// bucket while any other genuine Kind difference (e.g. `Bool` vs `Int`)
/// lands in separate ones.
pub(crate) fn canonical_bucket_kind(k: &Kind) -> Kind {
    match k {
        Kind::Int64 => Kind::Int,
        other => other.clone(),
    }
}

/// The Kind signature that determines which bucket a `SemFunctionDef` falls
/// into — see `check_overload_kind_agreement`. Deliberately **param Kinds
/// only**, not the return Kind: two overloads whose *parameter* Kinds differ
/// can never be confused at a call site (the argument's Kind already picks
/// the bucket, statically, with no domain check and therefore no merge point
/// to define), so their return Kinds are free to differ too. Two overloads
/// that share a parameter-Kind bucket, on the other hand, can be resolved
/// only by a domain check that may fall back to runtime dispatch — and an
/// unresolved runtime dispatch needs one canonical Kind to merge every
/// candidate's result into, which is exactly what same-bucket return-Kind
/// agreement (checked below) guarantees.
fn bucket_key(def: &SemFunctionDef) -> Vec<Kind> {
    def.param_kinds.iter().map(canonical_bucket_kind).collect()
}

/// `codegen::compile_call`'s built-in identity/cardinality calls — never
/// user-declared, so absent from `fn_sigs`. `from`/`size`/`len` always
/// return `Kind::Int`; `show` (string interpolation, `parser::expr`'s
/// `desugar_interp_parts`) always returns `Kind::Vector(Char)` (`Char*`)
/// instead — like the other three, its return Kind never depends on the
/// argument's Kind, it's just a different constant one. `show`'s codegen
/// (`codegen::show::compile_show`) recurses through the argument's actual
/// Kind at compile time to decide *how* to build that `Char*`, but nothing
/// here needs to know that.
fn builtin_call_kind(callee: &Symbol, args_len: usize, name_defs: &NameDefs) -> Option<Kind> {
    if args_len != 1 {
        return None;
    }
    if callee.0 == "show" {
        return Some(Kind::Vector(Box::new(Kind::Char)));
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
        // `char(n)` (this module's docs/design-decisions.md §13 "Char"):
        // like Signed32/Unsigned32, Char genuinely gets its own runtime Kind
        // (i32, disjoint from Int), so must be checked here too rather than
        // falling through to the `distinct`-only `Kind::Int` default below.
        Some(b) if b.kind == Kind::Char => Some(b.kind),
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
        Item::EquivDecl { lhs, rhs, span } => Ok(SemItem::EquivDecl {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            span: *span,
        }),
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
