//! Abstract value classifier — the shape of a Cantor value.
//!
//! This is the third layer of the three-layer value architecture:
//!   names  →  sets  →  Kind (abstract shape)
//!
//! `Kind` is a shared abstract classifier used by both the solver (to decide how
//! to extract counterexample values) and the code generator (to select LLVM wire
//! types).  LLVM-specific wire-type helpers (leaf counts, range/param kind
//! derivation) live in `codegen::wire`.
//!
//! Many set names share the same Kind (e.g. `Nat`, `NatPos`, and `Int16` are
//! all `Kind::Int`).

use crate::ast::{BinOp, DefKind, Expr, ExprKind, NameDefs, flatten_domain, flatten_disjoint_union};

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
    /// slots to hold the widest arm (see `codegen::wire::tagged_union_leaf_count`).
    /// Bool fields are zero-extended to i64; tuple fields are serialised leaf-by-leaf.
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



