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
    /// i64 (pointer-as-i64) — heap-allocated sorted array; element kind tracked for dispatch.
    Set(SetElemKind),
    /// LLVM struct — anonymous product type `(A, B, …)`.
    Tuple(Vec<Kind>),
    /// i64 (Stage 2: same wire type as Int) — disjoint union `A + B`.
    ///
    /// Each element is the Kind of one arm, in declaration order.
    /// TODO(Stage 3): replace the i64 wire type with a tagged `{i32 tag, <payload>}` struct
    /// once `match` and `distinct`-arm discrimination are implemented.
    Union(Vec<Kind>),
}

/// The runtime Kind of a value drawn from `set_expr`.
pub fn set_kind(set_expr: &Expr) -> Kind {
    match &set_expr.kind {
        ExprKind::Var(sym) if sym.0 == "Bool" => Kind::Bool,
        // `Set(Int)` / `Set(Bool)` — the power set of the given element set.
        ExprKind::Call { callee, args } if callee.0 == "Set" && args.len() == 1 => {
            match set_kind(&args[0]) {
                Kind::Bool => Kind::Set(SetElemKind::Bool),
                _ => Kind::Set(SetElemKind::Int),
            }
        }
        // `A * B * C` — Cartesian product → tuple.
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            let parts = flatten_domain(set_expr);
            Kind::Tuple(parts.into_iter().map(set_kind).collect())
        }
        // `A + B + C` — disjoint union → Union.
        ExprKind::BinOp { op: BinOp::Add, .. } => {
            let arms = flatten_disjoint_union(set_expr);
            Kind::Union(arms.into_iter().map(set_kind).collect())
        }
        _ => Kind::Int,
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
            if sym.0 == "Fail" { Kind::Int } else { set_kind(range) }
        }
        // `A | B` — plain union; dominant-kind rule strips Fail/Union wrappers so
        // the success-path kind is not masked by the failure arm.
        // `Fail * Y` arms (desugared from `!!`) are also stripped: they are always
        // failure-only and do not contribute to the success wire kind.
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            if is_fail_arm(lhs) { return range_kind(rhs); }
            if is_fail_arm(rhs) { return range_kind(lhs); }
            let lk = range_kind(lhs);
            let rk = range_kind(rhs);
            // Set dominates Bool dominates Tuple dominates Int.
            match (lk, rk) {
                (Kind::Set(ek), _) => Kind::Set(ek),
                (_, Kind::Set(ek)) => Kind::Set(ek),
                (Kind::Bool, _) | (_, Kind::Bool) => Kind::Bool,
                (Kind::Tuple(ek), _) => Kind::Tuple(ek),
                (_, Kind::Tuple(ek)) => Kind::Tuple(ek),
                _ => Kind::Int,
            }
        }
        // `A + B + C` — disjoint union; each arm retains its own kind.
        ExprKind::BinOp { op: BinOp::Add, .. } => {
            let arms = flatten_disjoint_union(range);
            Kind::Union(arms.into_iter().map(range_kind).collect())
        }
        _ => set_kind(range),
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
