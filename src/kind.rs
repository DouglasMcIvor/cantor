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

use crate::ast::{UnOp, BinOp, DefKind, Expr, ExprKind, NameDefs, flatten_domain, flatten_disjoint_union};
use crate::semantics::builtins;

/// The element kind of a homogeneous runtime set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetElemKind {
    Int,
    Bool,
}

// TODO: We should call this "Value" and move it into a semantics namespace
//       OR we should split it into Atom, Algebra?
//       We need to make a SemanticTree that an "elaboration" pass produces from the AST
//       that is what annotates the Kind and distinguishes "+" from context
//       Then the solver will produce a ConstrainedTree
/// All the possible fundamental Cantor values
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

// TODO: This appears to be growing into the Kind of any expression, not just sets
pub fn set_kind(set_expr: &Expr, name_defs: &NameDefs) -> Kind {
    match &set_expr.kind {
        ExprKind::IntLit { .. } => Kind::Int,
        ExprKind::BoolLit { .. } => Kind::Bool,
        ExprKind::Var(sym) => {
            if let Some(builtin) = builtins::lookup(&sym.0) {
                builtin.kind
            } else if let Some(def) = name_defs.get(sym) {
                match def.kind {
                    DefKind::Alias => set_kind(&def.value, name_defs),
                    // Distinct sets are always integer-backed at the LLVM level.
                    DefKind::Distinct => Kind::Int,
                }
            } else {
                // TODO: Compile error
                unreachable!("set_kind: unknown set name `{}`", sym.0)
            }
        }
        ExprKind::BinOp { op, lhs, rhs } => {
            binop_kind(op, lhs, rhs, name_defs)
        }
        ExprKind::UnOp { op, expr, .. } => {
            unop_kind(op, expr, name_defs)
        }
        // TODO: "Set" should also be part of the built in symbol table
        // `Set(Int)` / `Set(Bool)` — the power set of the given element set.
        ExprKind::Call { callee, args } => {
            if callee.0 == "Set" && args.len() == 1 {
                // TODO replace SetElemKind with just a nested Kind
                match set_kind(&args[0], name_defs) {
                    Kind::Bool => Kind::Set(SetElemKind::Bool),
                    Kind::Int => Kind::Set(SetElemKind::Int),
                    _ => unreachable!("{}", format!("Unexpected set element kind {set_expr:?}")),
                }
            } else {
                // TODO: Compile error
                unreachable!("set_kind: unknown compile time function name `{}`", callee.0)
            }
        }
        ExprKind::If { then_expr,else_expr, .. } => {
            merge_into_union(set_kind(then_expr, name_defs), set_kind(else_expr, name_defs))
        }
        // `{0, 1, 2}` as a set-builder expression — describes a domain restriction
        // to these elements, so its Kind is the *element* Kind (Int/Bool), not
        // `Kind::Set` (which is reserved for genuine runtime Set values, e.g. the
        // result of the `Set(Int)` constructor). `set_kind` is only ever called on
        // set-describing expressions (domain/range positions), never on arbitrary
        // value expressions, so this context assumption always holds.
        ExprKind::SetLit(exprs) => {
            let kinds = exprs.iter().map(|e| set_kind(e, name_defs)).collect();
            match union_if_distinct(kinds) {
                elem_kind @ (Kind::Int | Kind::Bool) => elem_kind,
                _ => unimplemented!("Sets may currently only contain values representable as Int or Bool")
            }
        }
        ExprKind::Try(expr) => set_kind(expr, name_defs),
        ExprKind::FailLit => Kind::Fail,
        ExprKind::FailWith(expr) => set_kind(expr, name_defs),
        ExprKind::Comprehension { source, .. } => {
            set_kind(source, name_defs)
        }
        ExprKind::Tuple(exprs) => {
            Kind::Tuple(exprs.into_iter().map(|p| set_kind(p, name_defs)).collect())
        }
        ExprKind::Proj { base, .. } => set_kind(base, name_defs),
        ExprKind::Index { base, .. } => set_kind(base, name_defs),
        ExprKind::KleeneStar(inner) => Kind::Vector(Box::new(set_kind(inner, name_defs)))
    }
}

fn binop_kind(bin_op: &BinOp, lhs: &Box<Expr>, rhs: &Box<Expr>, name_defs: &NameDefs) -> Kind {
    match &bin_op {
        // TODO: this is also "add" we need to know the context, doesn't the parser do this?
        // `A + B` — disjoint union. Unlike `|`, `+` *forces* disjointness (akin to
        // `distinct`): arms are never deduplicated by Kind, even when they share
        // the same underlying Kind (e.g. `{0} + NatPos` is still tagged), so the
        // result is always a TaggedUnion, never a bare Kind.
        BinOp::Add => {
            let left_parts = flatten_disjoint_union(lhs);
            let right_parts = flatten_disjoint_union(rhs);
            Kind::TaggedUnion(left_parts
                .into_iter()
                .chain(right_parts)
                .map(|p| set_kind(p, name_defs))
                .collect())
        }
        // TODO: this is also "sub" we need to know the context, doesn't the parser do this?
        // `A - B` — set difference.
        BinOp::Sub => {
            set_kind(lhs, name_defs)
        }
        // TODO: this is also "mul" we need to know the context, doesn't the parser do this?
        // `A * B * C` — Cartesian product → tuple.
        BinOp::Mul => {
            let left_parts = flatten_domain(lhs);
            let right_parts = flatten_domain(rhs);
            Kind::Tuple(left_parts
                .into_iter()
                .chain(right_parts)
                .map(|p| set_kind(p, name_defs))
                .collect())
        }
        // TODO: this will be both "div" and set quotient, again need context
        BinOp::Div => set_kind(lhs, name_defs),

        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Kind::Bool,
        BinOp::In | BinOp::NotIn => Kind::Bool,

        // `A | B` — union
        BinOp::Union => {
            merge_into_union(set_kind(lhs, name_defs), set_kind(rhs, name_defs))
        }
        // `A & B` — set intersection.
        BinOp::Intersect => set_kind(lhs, name_defs),
        // `A ^ B` — symmetric difference.
        BinOp::SymDiff => {
            merge_into_union(set_kind(lhs, name_defs), set_kind(rhs, name_defs))
        }
        BinOp::Concat => set_kind(lhs, name_defs),

        BinOp::And | BinOp::Or => Kind::Bool,
    }
}

fn unop_kind(un_op: &UnOp, expr: &Box<Expr>, name_defs: &NameDefs) -> Kind {
    match &un_op {
        UnOp::Not => Kind::Bool,
        UnOp::Neg => set_kind(expr, name_defs),
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



