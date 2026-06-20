//! Runtime value kinds — the LLVM representation a Cantor value compiles to.
//!
//! This is the third layer of the three-layer value architecture:
//!   names  →  sets  →  runtime Kind
//!
//! Kind is a pure codegen concept derived from a set expression.  The solver
//! works at the set layer and has no notion of Kind.  Many set names can share
//! the same Kind (e.g. `Nat`, `NatPos`, and `Int16` are all `Kind::Int`).

use crate::ast::{BinOp, Expr, ExprKind, FunctionSig};

/// The LLVM type a Cantor value compiles to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// i64 — integers, all named integer subsets (Nat, NatPos, Int8 … Int64, …)
    Int,
    /// i1 — the two-element Bool set {true, false}, disjoint from all integers
    Bool,
}

/// The runtime Kind of a value drawn from `set_expr`.
///
/// `Bool` is the only non-integer kind so far; every other named set and set
/// expression falls back to `Kind::Int`.
pub fn set_kind(set_expr: &Expr) -> Kind {
    match &set_expr.kind {
        ExprKind::Var(sym) if sym.0 == "Bool" => Kind::Bool,
        _ => Kind::Int,
    }
}

/// The runtime Kind of a function's return value, given its range expression.
///
/// `Fail` is the out-of-band failure sentinel and does not change the Kind of
/// the successful return values; it is stripped before inspecting the union.
pub fn range_kind(range: &Expr) -> Kind {
    match &range.kind {
        ExprKind::Var(sym) => {
            if sym.0 == "Fail" { Kind::Int } else { set_kind(range) }
        }
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            let lk = range_kind(lhs);
            let rk = range_kind(rhs);
            if lk == Kind::Bool || rk == Kind::Bool { Kind::Bool } else { Kind::Int }
        }
        _ => set_kind(range),
    }
}

/// The per-parameter Kinds for a function signature's domain.
///
/// Returns an empty vec for zero-argument functions (domain is `None`).
pub fn param_kinds(sig: &FunctionSig) -> Vec<Kind> {
    match &sig.domain {
        None => vec![],
        Some(domain) => flatten_domain(domain).into_iter().map(set_kind).collect(),
    }
}

/// Flatten a left-associative `A * B * C` product into `[A, B, C]`.
fn flatten_domain(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs } => {
            let mut parts = flatten_domain(lhs);
            parts.push(rhs);
            parts
        }
        _ => vec![expr],
    }
}
