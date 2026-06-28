//! Runtime value kinds — the LLVM representation a Cantor value compiles to.
//!
//! This is the third layer of the three-layer value architecture:
//!   names  →  sets  →  runtime Kind
//!
//! Kind is a pure codegen concept derived from a set expression.  The solver
//! works at the set layer and has no notion of Kind.  Many set names can share
//! the same Kind (e.g. `Nat`, `NatPos`, and `Int16` are all `Kind::Int`).

use crate::ast::{BinOp, Expr, ExprKind, FunctionSig};

/// The element kind of a homogeneous runtime set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetElemKind {
    Int,
    Bool,
}

/// The LLVM type a Cantor value compiles to.
///
/// `Copy` was intentionally dropped when `Tuple(Vec<Kind>)` was added; use
/// `.clone()` where a copy was previously implicit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// i64 — integers, all named integer subsets (Nat, NatPos, Int8 … Int64, …)
    Int,
    /// i1 — the two-element Bool set {true, false}, disjoint from all integers
    Bool,
    /// i1 — the `fail` singleton; always has value 1 when constructed.
    /// Used as the flag field in `{i1, i64}` fallible-function return structs.
    Fail,
    /// i64 (pointer-as-i64) — heap-allocated sorted array; element kind tracked for dispatch.
    Set(SetElemKind),
    /// LLVM struct — anonymous product type `(A, B, …)`.
    Tuple(Vec<Kind>),
    /// `{ i32 tag, i64 leaf_0, …, i64 leaf_N }`
    ///
    /// `tag` is the zero-based arm index.  The remaining fields are enough i64
    /// slots to hold the widest arm (see `tagged_union_leaf_count`).  Bool fields
    /// are zero-extended to i64; tuple fields are serialised leaf-by-leaf.
    TaggedUnion(Vec<Kind>),
    /// Variable-length sequence of `elem` values — the runtime representation of `X*`.
    /// Wire type: i64 (pointer-as-i64) to a heap-allocated Apache Arrow array.
    Vector(Box<Kind>),
}

/// The runtime Kind of a value drawn from `set_expr`.
pub fn set_kind(set_expr: &Expr) -> Kind {
    match &set_expr.kind {
        //TODO: central location for symbols rather than string matching here
        //TODO: we actually need to know how the symbol was defined, e.g. MyNat = Nat!
        ExprKind::Var(sym) if sym.0 == "Bool" => Kind::Bool,
        ExprKind::Var(sym) if sym.0 == "Int" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "Nat" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "NatPos" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "NonZeroInt" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "Int8" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "Int16" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "Int32" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "Int64" => Kind::Int,
        ExprKind::Var(sym) if sym.0 == "Fail" => Kind::Fail,
        ExprKind::SetLit(exprs) => {
            let kinds = exprs.iter().map(|e| set_kind(&e)).collect();
            let elem_kind = union_if_distinct(kinds);
            match elem_kind {
                Kind::Int => Kind::Set(SetElemKind::Int),
                Kind::Bool => Kind::Set(SetElemKind::Bool),
                _ => unimplemented!("Sets may currently only contain values representable as Int or Bool")
            }
        }
        // `Set(Int)` / `Set(Bool)` — the power set of the given element set.
        ExprKind::Call { callee, args } if callee.0 == "Set" && args.len() == 1 => {
            match set_kind(&args[0]) {
                Kind::Bool => Kind::Set(SetElemKind::Bool),
                Kind::Int => Kind::Set(SetElemKind::Int),
                // TODO should this be a compile error instead?
                _ => unreachable!("{}", format!("Unexpected set element kind {set_expr:?}")),
            }
        }
        // `A * B * C` — Cartesian product → tuple.
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            let parts = flatten_domain(set_expr);
            Kind::Tuple(parts.into_iter().map(set_kind).collect())
        }
        // `A - B`, `A & B` — set difference, intersection.
        // The result is a subset of A, so its kind is A's kind.
        ExprKind::BinOp { op: BinOp::Sub | BinOp::Intersect, lhs, .. } => {
            set_kind(lhs)
        }
        // `A ^ B` — symmetric difference.
        // The result contains elements from A *and* elements from B, so when the two
        // sides have different kinds the result is their union kind.
        ExprKind::BinOp { op: BinOp::SymDiff, lhs, rhs, .. } => {
            merge_into_union(set_kind(lhs), set_kind(rhs))
        }
        // `A + B` — disjoint union
        ExprKind::BinOp { op: BinOp::Add, .. } => {
            // Don't merge the individual Kinds when the union is disjoint
            let parts = flatten_disjoint_union(set_expr);
            Kind::TaggedUnion(parts.into_iter().map(set_kind).collect())
        }
        // `A | B` — union
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs, .. } => {
            merge_into_union(set_kind(lhs), set_kind(rhs))
        }
        ExprKind::KleeneStar(inner) => Kind::Vector(Box::new(set_kind(inner))),
        _ => unreachable!("{}", format!("Unexpected expression kind {set_expr:?}")),
    }
}

/// Number of i64 leaf fields when a Kind is serialised into a tagged-union payload.
/// Bool and Int each occupy one slot; Tuple recurses into its element kinds.
pub fn leaf_count(kind: &Kind) -> usize {
    match kind {
        Kind::Bool | Kind::Int | Kind::Set(_) | Kind::Fail => 1,
        Kind::Tuple(elems) => elems.iter().map(leaf_count).sum(),
        Kind::TaggedUnion(arms) => 1 + tagged_union_leaf_count(arms),
        // Vector is an i64 pointer (like Set) — one leaf.
        Kind::Vector(_) => 1,
    }
}

/// Maximum leaf count over all arms; gives the payload width of the tagged-union struct.
pub fn tagged_union_leaf_count(arms: &[Kind]) -> usize {
    arms.iter().map(leaf_count).max().unwrap_or(0)
}

/// Merge two Kinds into an atomic Kind or a Union
fn merge_into_union(lk: Kind, rk: Kind) -> Kind {
    let mut merged = into_union(lk);
    merged.extend(into_union(rk));
    union_if_distinct(merged)
}

fn union_if_distinct(kinds: Vec<Kind>) -> Kind {
    let mut unique = Vec::new();
    for kind in kinds {
        if !unique.contains(&kind) {
            unique.push(kind);
        }
    }

    if unique.len() == 1 {
        unique.pop().unwrap()
    } else {
        Kind::TaggedUnion(unique)
    }
}

/// Convert any Kind into a TaggedUnion of one element, if it isn't one already
fn into_union(kind: Kind) -> Vec<Kind> {
    match kind {
        Kind::TaggedUnion(v) => v,
        k => vec![k],
    }
}

/// Flatten a left-associated disjoint union `((A + B) + C)` into `[A, B, C]`.
pub fn flatten_disjoint_union(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Add, lhs, rhs } => {
            let mut arms = flatten_disjoint_union(lhs);
            arms.extend(flatten_disjoint_union(rhs));
            arms
        }
        _ => vec![expr],
    }
}

/// True if an expression is a pure failure arm — either bare `Fail` or `Fail * Y`
/// (the desugared form of `!! Y`).  These arms do not contribute to the success
/// wire kind and are stripped by `range_kind`'s Union rule.
fn is_fail_arm(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Var(sym) if sym.0 == "Fail" => true,
        ExprKind::BinOp { op: BinOp::Mul, lhs, .. } => {
            matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
        }
        _ => false,
    }
}

/// The runtime Kind of a function's return value, given its range expression.
///
/// `Fail` is the out-of-band failure sentinel and does not change the Kind of
/// the successful return values; it is stripped before inspecting the union.
pub fn range_kind(range: &Expr) -> Kind {
    match &range.kind {
        ExprKind::Var(sym) => {
            // Bare `Fail` has its own Kind; it becomes the flag field of {Fail, Int} structs.
            if sym.0 == "Fail" { Kind::Fail } else { set_kind(range) }
        }
        // `A | B` — any union with a fail arm produces the fallible struct wire type {i1, i64}.
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs, .. } => {
            fail_kind(range, lhs, rhs)
        }
        // `A + B + C` — disjoint union; each arm retains its own kind.
        ExprKind::BinOp { op: BinOp::Add, lhs, rhs, .. } => {
            fail_kind(range, lhs, rhs)
        }
        _ => set_kind(range),
    }
}

fn fail_kind(range: &Expr, lhs: &Expr, rhs: &Expr) -> Kind {
    if is_fail_arm(lhs) {
        Kind::Tuple(vec![Kind::Fail, set_kind(rhs)])
    } else if is_fail_arm(rhs) {
        Kind::Tuple(vec![Kind::Fail, set_kind(lhs)])
    } else {
        set_kind(range)
    }
}

/// The per-parameter Kinds for a function signature's domain.
///
/// `n_params` is `def.params.len()` — the number of named parameters in the
/// function definition.  Uses `param_set_exprs` so that a single-tuple-param
/// function yields `[Kind::Tuple(...)]` rather than the individual element kinds.
///
/// Returns an empty vec for zero-argument functions (domain is `None`).
pub fn param_kinds(sig: &FunctionSig, n_params: usize) -> Vec<Kind> {
    match param_set_exprs(sig.domain.as_ref(), n_params) {
        Ok(parts) => parts.into_iter().map(set_kind).collect(),
        Err(_) => vec![Kind::Int; n_params],
    }
}

/// Map each function parameter to its set expression, implementing the
/// arity disambiguation rule:
///
/// - `parts.len() == n_params` → N scalar params (each part is one param's set).
/// - `n_params == 1` and `parts.len() > 1` → the single param is a tuple whose
///   set is the entire domain expression.
/// - Otherwise → arity error.
pub fn param_set_exprs<'a>(domain: Option<&'a Expr>, n_params: usize) -> Result<Vec<&'a Expr>, String> {
    match domain {
        None if n_params == 0 => Ok(vec![]),
        None => Err(format!("domain has 0 parts but function has {n_params} parameters")),
        Some(domain_expr) => {
            let parts = flatten_domain(domain_expr);
            if parts.len() == n_params {
                Ok(parts)
            } else if n_params == 1 {
                // Single tuple parameter covering the whole product domain.
                Ok(vec![domain_expr])
            } else {
                Err(format!(
                    "domain arity {} doesn't match parameter count {}",
                    parts.len(), n_params
                ))
            }
        }
    }
}

/// Flatten a left-associative `A * B * C` product into `[A, B, C]`.
pub(crate) fn flatten_domain(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs } => {
            let mut parts = flatten_domain(lhs);
            parts.push(rhs);
            parts
        }
        _ => vec![expr],
    }
}
