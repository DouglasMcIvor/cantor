//! Runtime value kinds — the LLVM representation a Cantor value compiles to.
//!
//! This is the third layer of the three-layer value architecture:
//!   names  →  sets  →  runtime Kind
//!
//! Kind is a pure codegen concept derived from a set expression.  The solver
//! works at the set layer and has no notion of Kind.  Many set names can share
//! the same Kind (e.g. `Nat`, `NatPos`, and `Int16` are all `Kind::Int`).

use crate::ast::{BinOp, DefKind, Expr, ExprKind, FunctionSig, NameDefs, flatten_domain, flatten_disjoint_union, param_set_exprs};

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
pub fn set_kind(set_expr: &Expr, name_defs: &NameDefs) -> Kind {
    match &set_expr.kind {
        ExprKind::Var(sym) => match sym.0.as_str() {
            "Bool" => Kind::Bool,
            "Int" | "Nat" | "NatPos" | "NonZeroInt"
            | "Int8" | "Int16" | "Int32" | "Int64" => Kind::Int,
            "Fail" => Kind::Fail,
            _ => {
                // Resolve user-defined names through the symbol table.
                if let Some(def) = name_defs.get(sym) {
                    match def.kind {
                        DefKind::Alias => set_kind(&def.value, name_defs),
                        // Distinct sets are always integer-backed at the LLVM level.
                        DefKind::Distinct => Kind::Int,
                    }
                } else {
                    unreachable!("set_kind: unknown set name `{}` — not a built-in and not in name_defs", sym.0)
                }
            }
        },
        ExprKind::SetLit(exprs) => {
            let kinds = exprs.iter().map(|e| set_kind(e, name_defs)).collect();
            let elem_kind = union_if_distinct(kinds);
            match elem_kind {
                Kind::Int => Kind::Set(SetElemKind::Int),
                Kind::Bool => Kind::Set(SetElemKind::Bool),
                _ => unimplemented!("Sets may currently only contain values representable as Int or Bool")
            }
        }
        // `Set(Int)` / `Set(Bool)` — the power set of the given element set.
        ExprKind::Call { callee, args } if callee.0 == "Set" && args.len() == 1 => {
            match set_kind(&args[0], name_defs) {
                Kind::Bool => Kind::Set(SetElemKind::Bool),
                Kind::Int => Kind::Set(SetElemKind::Int),
                // TODO should this be a compile error instead?
                _ => unreachable!("{}", format!("Unexpected set element kind {set_expr:?}")),
            }
        }
        // `A * B * C` — Cartesian product → tuple.
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            let parts = flatten_domain(set_expr);
            Kind::Tuple(parts.into_iter().map(|p| set_kind(p, name_defs)).collect())
        }
        // `A - B`, `A & B` — set difference, intersection.
        // The result is a subset of A, so its kind is A's kind.
        ExprKind::BinOp { op: BinOp::Sub | BinOp::Intersect, lhs, .. } => {
            set_kind(lhs, name_defs)
        }
        // `A ^ B` — symmetric difference.
        // The result contains elements from A *and* elements from B, so when the two
        // sides have different kinds the result is their union kind.
        ExprKind::BinOp { op: BinOp::SymDiff, lhs, rhs, .. } => {
            merge_into_union(set_kind(lhs, name_defs), set_kind(rhs, name_defs))
        }
        // `A + B` — disjoint union
        ExprKind::BinOp { op: BinOp::Add, .. } => {
            let parts = flatten_disjoint_union(set_expr);
            Kind::TaggedUnion(parts.into_iter().map(|p| set_kind(p, name_defs)).collect())
        }
        // `A | B` — union
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs, .. } => {
            merge_into_union(set_kind(lhs, name_defs), set_kind(rhs, name_defs))
        }
        ExprKind::KleeneStar(inner) => Kind::Vector(Box::new(set_kind(inner, name_defs))),
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
pub fn range_kind(range: &Expr, name_defs: &NameDefs) -> Kind {
    match &range.kind {
        ExprKind::Var(sym) => {
            // Bare `Fail` has its own Kind; it becomes the flag field of {Fail, Int} structs.
            if sym.0 == "Fail" { Kind::Fail } else { set_kind(range, name_defs) }
        }
        // `A | B` — any union with a fail arm produces the fallible struct wire type {i1, i64}.
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs, .. } => {
            fail_kind(range, lhs, rhs, name_defs)
        }
        // `A + B + C` — disjoint union; each arm retains its own kind.
        ExprKind::BinOp { op: BinOp::Add, lhs, rhs, .. } => {
            fail_kind(range, lhs, rhs, name_defs)
        }
        _ => set_kind(range, name_defs),
    }
}

fn fail_kind(range: &Expr, lhs: &Expr, rhs: &Expr, name_defs: &NameDefs) -> Kind {
    if is_fail_arm(lhs) {
        Kind::Tuple(vec![Kind::Fail, set_kind(rhs, name_defs)])
    } else if is_fail_arm(rhs) {
        Kind::Tuple(vec![Kind::Fail, set_kind(lhs, name_defs)])
    } else {
        set_kind(range, name_defs)
    }
}

/// The per-parameter Kinds for a function signature's domain.
///
/// `n_params` is `def.params.len()` — the number of named parameters in the
/// function definition.  Uses `param_set_exprs` so that a single-tuple-param
/// function yields `[Kind::Tuple(...)]` rather than the individual element kinds.
///
/// Returns an empty vec for zero-argument functions (domain is `None`).
pub fn param_kinds(sig: &FunctionSig, n_params: usize, name_defs: &NameDefs) -> Vec<Kind> {
    match param_set_exprs(sig.domain.as_ref(), n_params) {
        Ok(parts) => parts.into_iter().map(|p| set_kind(p, name_defs)).collect(),
        Err(_) => vec![Kind::Int; n_params],
    }
}

