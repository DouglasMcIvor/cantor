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
use crate::kind::{Kind, is_distinct_basis_representable, set_kind};
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
/// user-declared, so absent from `fn_sigs`. `size`/`len` always return
/// `Kind::Int`; `show` (string interpolation, `parser::expr`'s
/// `desugar_interp_parts`) always returns `Kind::Vector(Char)` (`Char*`)
/// instead — like `size`/`len`, its return Kind never depends on the
/// argument's Kind, it's just a different constant one. `show`'s codegen
/// (`codegen::show::compile_show`) recurses through the argument's actual
/// Kind at compile time to decide *how* to build that `Char*`, but nothing
/// here needs to know that. `from(x)` is the one exception: since `distinct`
/// is Kind-transparent (see `set_kind`'s `DefKind::Distinct` arm), `x`'s own
/// already-elaborated Kind already *is* its distinct set's basis Kind, so
/// `from(x)`'s return Kind is just `x`'s Kind, unchanged — hence this takes
/// the elaborated `args`, not merely a count. `Char`/`Signed32`/`Unsigned32`
/// are the exception: those genuinely get their own runtime Kind different
/// from their `Int` basis (see `builtins::lookup`), so `from(x)` on one of
/// those is real conversion work, not identity — `codegen::expr_call`'s
/// `from(x)` arm already sign-/zero-extends and tags back up to `Kind::Int`
/// for exactly these three; this must agree with that, not with the
/// Kind-transparent case above.
fn builtin_call_kind(callee: &Symbol, args: &[SemExpr], name_defs: &NameDefs) -> Option<Kind> {
    let [arg] = args else { return None };
    if callee.0 == "show" {
        return Some(Kind::Vector(Box::new(Kind::Char)));
    }
    if callee.0 == "from" {
        return Some(match arg.kind_of {
            Kind::Char | Kind::Signed32 | Kind::Unsigned32 => Kind::Int,
            ref k => k.clone(),
        });
    }
    if callee.0 == "size" || callee.0 == "len" {
        return Some(Kind::Int);
    }
    // Auto-generated constructor `Name.Label(x)` for a named union arm
    // (`Name = distinct (Label: Expr | ...)`) — same basis-Kind result as
    // any other `distinct` constructor below, just keyed by the dotted
    // callee name instead of a single capitalized identifier.
    if let Some((name_part, label_part)) = callee.0.split_once('.') {
        let found = name_defs.get(&Symbol::new(name_part)).and_then(|def| {
            (def.kind == DefKind::Distinct
                && def
                    .labels
                    .as_ref()
                    .is_some_and(|labels| labels.iter().any(|l| l.0 == label_part)))
            .then_some(def)
        });
        if let Some(def) = found {
            return set_kind(&def.value, name_defs).ok();
        }
    }
    let mut chars = callee.0.chars();
    let first = chars.next()?;
    let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
    // Auto-generated constructor for a wrapping fixed-width integer builtin
    // (`signed32(n)`/`unsigned32(n)`, docs/wrapping-and-quotient-sets-
    // plan.md): unlike `distinct`, a wrapping sort genuinely gets its own
    // runtime Kind (different LLVM width/ABI extension), so this must be
    // checked *before* falling through to the `distinct` default below.
    match crate::semantics::builtins::lookup(&capitalized) {
        Some(b) if b.kind == Kind::Signed32 || b.kind == Kind::Unsigned32 => Some(b.kind),
        // `char(n)` (this module's docs/design-decisions.md §13 "Char"):
        // like Signed32/Unsigned32, Char genuinely gets its own runtime Kind
        // (i32, disjoint from Int), so must be checked here too rather than
        // falling through to the `distinct` default below.
        Some(b) if b.kind == Kind::Char => Some(b.kind),
        _ => {
            // Auto-generated constructor `d(x)` for `D = distinct B` — the
            // constructor's result Kind is `B`'s own Kind (`distinct` is
            // Kind-transparent, see `set_kind`'s `DefKind::Distinct` arm).
            match name_defs.get(&Symbol(capitalized)) {
                Some(def) if def.kind == DefKind::Distinct => set_kind(&def.value, name_defs).ok(),
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
        .map(|sig| elaborate_sig(sig, &def.params, def.params.len(), ctx))
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
    params: &[ast::Param],
    n_params: usize,
    ctx: &Ctx,
) -> Result<SemFunctionSig, CompileError> {
    let mut env = Env::new();
    let guarded_domain = desugar_param_guards(sig, params, n_params)?;
    let domain = guarded_domain
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

/// Desugar per-parameter guards (`x for <pred>`) into the domain a user
/// could already write by hand: `x for pred` on parameter `i` narrows that
/// parameter's already-declared domain slice to `{x for x in <slice> if
/// pred}`, reusing the existing comprehension machinery end to end (solver,
/// codegen) with zero new `SemExprKind`. No-op (returns `sig.domain`
/// unchanged, no clone) when no parameter carries a guard.
fn desugar_param_guards(
    sig: &ast::FunctionSig,
    params: &[ast::Param],
    n_params: usize,
) -> Result<Option<ast::Expr>, CompileError> {
    if !params.iter().any(|p| p.guard.is_some()) {
        return Ok(sig.domain.clone());
    }
    let parts = ast::param_set_exprs(sig.domain.as_ref(), n_params).map_err(CompileError::ice)?;
    let wrapped = parts.iter().zip(params.iter()).map(|(part, param)| {
        let part = (*part).clone();
        match &param.guard {
            None => part,
            Some(pred) => {
                let span = part.span;
                ast::Expr::new(
                    ast::ExprKind::Comprehension {
                        output: Box::new(ast::Expr::new(
                            ast::ExprKind::Var(param.name.clone()),
                            span,
                        )),
                        var: param.name.clone(),
                        source: Box::new(part),
                        filter: Some(Box::new(pred.clone())),
                    },
                    span,
                )
            }
        }
    });
    let combined = wrapped
        .reduce(|acc, next| {
            let span = Span::new(acc.span.start, next.span.end);
            ast::Expr::new(
                ast::ExprKind::BinOp {
                    op: ast::BinOp::Mul,
                    lhs: Box::new(acc),
                    rhs: Box::new(next),
                },
                span,
            )
        })
        .expect("n_params > 0 whenever a param has a guard, so parts is non-empty");
    Ok(Some(combined))
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
    if def.kind == DefKind::Distinct {
        validate_distinct_basis(def, &value)?;
    }
    Ok(SemNameDef {
        name: def.name.clone(),
        kind: def.kind,
        ty,
        value,
        labels: def.labels.clone(),
        span: def.span,
    })
}

/// Validate a `Distinct` def's basis — every `D = distinct B` def, not just
/// labeled named unions (an unlabeled `Litre = distinct Bool` needs the same
/// validation as a labeled one).
///
/// Two shapes are accepted:
/// - A single, solver-representable Kind (`kind::is_distinct_basis_representable`)
///   — covers plain `distinct` and today's same-Kind-arm named unions
///   (`Circle: Nat | Radius: NatPos`, both `Kind::Int`).
/// - A `Kind::TaggedUnion` (arms with genuinely different Kinds from each
///   other) *only* when labeled — an unlabeled `distinct` over a
///   heterogeneous union has no way to pick "which arm" a constructor
///   argument belongs to.
///
/// Arms are no longer required to have pairwise-distinct Kinds
/// (`Circle: Nat | Square: NatPos | Rect: Nat * Nat` — two `Int`-Kind arms
/// mixed with a `Tuple`-Kind one — is accepted): the solver- and codegen-
/// side gaps that motivated the earlier restriction are fixed —
/// `solver::encode_call::coerce_arg_to_labeled_arm` now selects a labeled
/// constructor's arm by its known position instead of searching by CVC5
/// sort (the old `coerce_to_union_dt` search silently collapsed same-Kind
/// labeled arms onto the same constructor — confirmed as real solver-level
/// unsoundness, `Shape.Circle(5)` and `Shape.Square(5)` provably "equal"),
/// `solver::membership_seq::membership_constraint_for_dt` matches a union
/// DT's constructors by position instead of by name (`arm_ctor_name`
/// derives a name purely from Kind, so same-Kind arms always collided on
/// the same declared name), and `codegen::compile::compile_elaborated`'s
/// `named_union_arms` table is built from each *syntactic* arm's own Kind
/// (`ast::flatten_union`) instead of the whole union's Kind-deduped arm
/// list (which silently dropped arms sharing a Kind, previously masked by
/// this very restriction never letting that code run).
fn validate_distinct_basis(def: &NameDef, value: &SemExpr) -> Result<(), CompileError> {
    let Kind::TaggedUnion(_) = &value.kind_of else {
        if !is_distinct_basis_representable(&value.kind_of) {
            return Err(not_yet_implemented(
                &format!(
                    "distinct basis of kind {:?} (`Set(_)` elements have no structural \
                     equality/ordering yet, see `kind::is_scalar_word_kind`)",
                    value.kind_of
                ),
                value.span,
            ));
        }
        return Ok(());
    };
    if def.labels.is_none() {
        return Err(not_yet_implemented(
            "an unlabeled `distinct` over arms of different Kinds — there's no way to pick \
             which arm a constructor argument belongs to without labels; write e.g. `distinct \
             (Circle: Nat | Rect: Nat * Nat)` instead",
            value.span,
        ));
    }
    // `value.kind_of`'s own `TaggedUnion` arm list is already deduped by Kind
    // (`kind::union_if_distinct`), so it can't be used to validate each
    // *syntactic* arm (`flatten_any_union`, one entry per `|`, never
    // deduped) — walk that list instead.
    let arms = flatten_any_union(value);
    if let Some(bad) = arms
        .iter()
        .find(|arm| !is_distinct_basis_representable(&arm.kind_of))
    {
        return Err(not_yet_implemented(
            &format!(
                "named union arm of kind {:?} has no representable solver sort",
                bad.kind_of
            ),
            bad.span,
        ));
    }
    Ok(())
}
