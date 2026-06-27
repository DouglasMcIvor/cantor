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
    /// i64 (Stage 2: same wire type as Int) — disjoint union `A + B`.
    ///
    /// Each element is the Kind of one arm, in declaration order.
    /// TODO(Stage 3): replace the i64 wire type with a tagged `{i32 tag, <payload>}` struct
    /// once `match` and `distinct`-arm discrimination are implemented.
    Union(Vec<Kind>),
    /// `{ i32 tag, i64 leaf_0, …, i64 leaf_N }` — cross-kind union `A | B | …`
    /// where at least one arm is a `Tuple`.
    ///
    /// `tag` is the zero-based arm index.  The remaining fields are enough i64
    /// slots to hold the widest arm (see `tagged_union_leaf_count`).  Bool fields
    /// are zero-extended to i64; tuple fields are serialised leaf-by-leaf.
    TaggedUnion(Vec<Kind>),
    /// Variable-length sequence of `elem` values — the runtime representation of `X*`.
    /// TODO: codegen not yet implemented; compile-time paths that call `leaf_count` or
    /// `arm_ctor_name` on a Vector will panic until the representation is decided.
    Vector(Box<Kind>),
}

/// The runtime Kind of a value drawn from `set_expr`.
pub fn set_kind(set_expr: &Expr) -> Kind {
    match &set_expr.kind {
        ExprKind::KleeneStar(inner) => Kind::Vector(Box::new(set_kind(inner))),
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
        // `A | B` — union in domain position.
        // Scalar-only unions share i64 ABI, no tag needed.
        // Any union involving a Tuple arm needs a tagged-union repr; flatten
        // nested unions so `(A | B) | C` produces a single TaggedUnion([A,B,C]).
        ExprKind::BinOp { op: BinOp::Union, .. } => {
            let arm_exprs = flatten_union(set_expr);
            let arm_kinds: Vec<Kind> = arm_exprs.into_iter().map(set_kind).collect();
            if arm_kinds.iter().any(|k| matches!(k, Kind::Tuple(_) | Kind::TaggedUnion(_))) {
                // Flatten any nested TaggedUnions that arose from recursive set_kind calls.
                let arms = flatten_tag_arms(arm_kinds);
                Kind::TaggedUnion(arms)
            } else {
                Kind::Int
            }
        }
        _ => Kind::Int,
    }
}

/// Number of i64 leaf fields when a Kind is serialised into a tagged-union payload.
/// Bool and Int each occupy one slot; Tuple recurses into its element kinds.
pub fn leaf_count(kind: &Kind) -> usize {
    match kind {
        Kind::Bool | Kind::Int | Kind::Set(_) | Kind::Fail | Kind::Union(_) => 1,
        Kind::Tuple(elems) => elems.iter().map(leaf_count).sum(),
        Kind::TaggedUnion(arms) => 1 + tagged_union_leaf_count(arms),
        // TODO: Vector codegen representation is not yet decided; panic loudly.
        Kind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in leaf_count"),
    }
}

/// Maximum leaf count over all arms; gives the payload width of the tagged-union struct.
pub fn tagged_union_leaf_count(arms: &[Kind]) -> usize {
    arms.iter().map(leaf_count).max().unwrap_or(0)
}

/// Flatten any `Kind::TaggedUnion` elements in `arms` into their inner arms,
/// producing a single flat list.  Used when building a TaggedUnion from nested
/// `|` expressions so that `(A | B) | C` gives `[A, B, C]` not `[[A,B], C]`.
fn flatten_tag_arms(arms: Vec<Kind>) -> Vec<Kind> {
    let mut out = Vec::with_capacity(arms.len());
    for k in arms {
        match k {
            Kind::TaggedUnion(inner) => out.extend(inner),
            other => out.push(other),
        }
    }
    out
}

/// Flatten a left-associated `|` union `((A | B) | C)` into `[A, B, C]`.
pub fn flatten_union(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            let mut arms = flatten_union(lhs);
            arms.extend(flatten_union(rhs));
            arms
        }
        _ => vec![expr],
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
        // Unions without fail arms: scalar-only uses the dominant-kind rule; any
        // Tuple arm triggers tagged-union IR (flatten n-ary unions as one TaggedUnion).
        ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
            if is_fail_arm(lhs) || is_fail_arm(rhs) {
                return Kind::Tuple(vec![Kind::Fail, Kind::Int]);
            }
            let arm_exprs = flatten_union(range);
            let arm_kinds: Vec<Kind> = arm_exprs.iter().map(|e| range_kind(e)).collect();
            if arm_kinds.iter().any(|k| matches!(k, Kind::Tuple(_) | Kind::TaggedUnion(_))) {
                let arms = flatten_tag_arms(arm_kinds);
                return Kind::TaggedUnion(arms);
            }
            // All scalar: Set dominates Bool dominates Int.
            if let Some(ek) = arm_kinds.iter().find_map(|k| match k { Kind::Set(e) => Some(*e), _ => None }) {
                Kind::Set(ek)
            } else if arm_kinds.iter().any(|k| *k == Kind::Bool) {
                Kind::Bool
            } else {
                Kind::Int
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
