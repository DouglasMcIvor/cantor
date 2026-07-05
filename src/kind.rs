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

use crate::ast::{
    BinOp, DefKind, Expr, ExprKind, NameDefs, UnOp, flatten_disjoint_union, flatten_domain,
};
use crate::error::CompileError;
use crate::semantics::builtins;

/// All the possible fundamental Cantor values
///
/// `Copy` was intentionally dropped when `Tuple(Vec<Kind>)` was added; use
/// `.clone()` where a copy was previously implicit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// i64 — the tagged/general integer representation. All named integer
    /// subsets (Nat, NatPos, Int8 … Int64, …) elaborate to this by default
    /// (`semantics::builtins::lookup`); it's the canonical shared Kind
    /// wherever an `Int`/`Int64` mismatch needs reconciling (e.g.
    /// `IfMerge::CoerceInt64ToInt`).
    Int,
    /// i64, raw/untagged — produced by `solver::int64_split`'s two
    /// compiler-generated transforms (int-soundness-plan phase 3): whole-
    /// function promotion when a function's domain is already a bounded
    /// `Int64` subset, and the solver-gated `Int64`/`BigInt` overload split
    /// otherwise. Every match on `Kind` added before these transforms
    /// existed treats this identically to `Kind::Int` (same wire type, same
    /// solver sort); the one place it's meant to diverge is
    /// `check_overload_kind_agreement`'s compiler-generated-split exception.
    Int64,
    /// i1 — the two-element Bool set {true, false}, disjoint from all integers
    Bool,
    /// i1 — the `fail` singleton; always has value 1 when constructed.
    /// Used as the flag field in `{i1, i64}` fallible-function return structs.
    Fail,
    /// i64 (pointer-as-i64) — heap-allocated sorted array of the boxed
    /// element Kind. Only single-i64-word Kinds (`Int`, `Int64`, `Bool`,
    /// `Fail`) can appear here today — `set_kind`'s `Set(X)` arm is the
    /// single place that enforces this; see `is_scalar_word_kind`.
    /// Anything else (`Tuple`, `TaggedUnion`, `Vector`, a nested `Set`)
    /// would need genuine structural equality/ordering to dedup and sort
    /// by value, which nothing in the compiler implements yet — not even
    /// `==` on a `Tuple`.
    Set(Box<Kind>),
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

/// The Kind of a set-*describing* expression (domain/range annotations, `let`
/// constraints, the RHS of `in`, …). Value-position expressions (function
/// bodies, `let` values, …) never call this — `semantics::elaborate`'s
/// `Position` enum decides structurally which one applies and only routes
/// set-position nodes here.
pub fn set_kind(set_expr: &Expr, name_defs: &NameDefs) -> Result<Kind, CompileError> {
    Ok(match &set_expr.kind {
        ExprKind::IntLit { .. } => Kind::Int,
        ExprKind::BoolLit { .. } => Kind::Bool,
        ExprKind::Var(sym) => {
            if let Some(builtin) = builtins::lookup(&sym.0) {
                builtin.kind
            } else if let Some(def) = name_defs.get(sym) {
                match def.kind {
                    DefKind::Alias => set_kind(&def.value, name_defs)?,
                    // Distinct sets are always integer-backed at the LLVM level.
                    DefKind::Distinct => Kind::Int,
                }
            } else {
                return Err(CompileError::UndefinedVariable {
                    name: sym.0.clone(),
                    span: set_expr.span,
                });
            }
        }
        ExprKind::BinOp { op, lhs, rhs } => binop_kind(op, lhs, rhs, name_defs)?,
        ExprKind::UnOp { op, expr, .. } => unop_kind(op, expr, name_defs)?,
        // `Set(Int)` / `Set(Bool)` / … — the power set of the given element set.
        ExprKind::Call { callee, args } => {
            if callee.0 == builtins::SET_CONSTRUCTOR && args.len() == 1 {
                let elem_kind = set_kind(&args[0], name_defs)?;
                if is_scalar_word_kind(&elem_kind) {
                    Kind::Set(Box::new(elem_kind))
                } else {
                    return Err(CompileError::Unsupported {
                        feature: format!(
                            "Set({elem_kind:?}) — runtime sets can only hold scalar \
                             elements (Int, Bool, Fail, and their named subsets) today"
                        ),
                        span: set_expr.span,
                    });
                }
            } else {
                return Err(CompileError::UndefinedFunction {
                    name: callee.0.clone(),
                    span: set_expr.span,
                });
            }
        }
        ExprKind::If {
            then_expr,
            else_expr,
            ..
        } => merge_into_union(
            set_kind(then_expr, name_defs)?,
            set_kind(else_expr, name_defs)?,
        ),
        // `{0, 1, 2}` as a set-builder expression — describes a domain restriction
        // to these elements, so its Kind is the *element* Kind, not `Kind::Set`
        // (which is reserved for genuine runtime Set values, e.g. the result of
        // the `Set(Int)` constructor). `set_kind` is only ever called on
        // set-describing expressions (domain/range positions), never on arbitrary
        // value expressions, so this context assumption always holds. Element
        // Kind isn't restricted to Int/Bool here — e.g. `Nat* - {[]}` needs
        // `{[]}`'s element Kind to be `Vector(Int)` to describe the excluded
        // empty-sequence value. Constructing a genuine *runtime* Set value
        // (Position::Value) is a separate, still-scalar-only restriction
        // enforced by `codegen::compile_set_lit_value`.
        ExprKind::SetLit(exprs) => {
            let kinds = exprs
                .iter()
                .map(|e| set_kind(e, name_defs))
                .collect::<Result<Vec<_>, _>>()?;
            union_if_distinct(kinds)
        }
        ExprKind::Try(expr) => set_kind(expr, name_defs)?,
        ExprKind::FailLit => Kind::Fail,
        ExprKind::FailWith(expr) => set_kind(expr, name_defs)?,
        ExprKind::Comprehension { source, .. } => set_kind(source, name_defs)?,
        ExprKind::Tuple(exprs) => Kind::Tuple(
            exprs
                .iter()
                .map(|p| set_kind(p, name_defs))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ExprKind::Proj { base, .. } => set_kind(base, name_defs)?,
        ExprKind::Index { base, .. } => set_kind(base, name_defs)?,
        ExprKind::KleeneStar(inner) => Kind::Vector(Box::new(set_kind(inner, name_defs)?)),
    })
}

/// Whether `kind` is representable as a single raw i64 word — the only
/// element kinds a runtime `Set(_)` can hold today. `Tuple`/`TaggedUnion`
/// (multi-leaf) and `Vector`/`Set` (pointer identity ≠ value equality) would
/// need genuine structural equality/ordering to dedup and sort by value,
/// which nothing in the compiler implements yet.
pub fn is_scalar_word_kind(kind: &Kind) -> bool {
    matches!(kind, Kind::Int | Kind::Int64 | Kind::Bool | Kind::Fail)
}

/// The set-position interpretation of each `BinOp`; only reached via
/// `set_kind`, so `Add`/`Sub`/`Mul`/`Div` here are always the set-operation
/// reading (disjoint union/difference/Cartesian product/quotient) — the
/// value-position arithmetic reading is decided separately and never calls
/// this (see `set_kind`'s doc comment).
fn binop_kind(
    bin_op: &BinOp,
    lhs: &Expr,
    rhs: &Expr,
    name_defs: &NameDefs,
) -> Result<Kind, CompileError> {
    Ok(match &bin_op {
        // `A + B` — disjoint union. Unlike `|`, `+` *forces* disjointness (akin to
        // `distinct`): arms are never deduplicated by Kind, even when they share
        // the same underlying Kind (e.g. `{0} + NatPos` is still tagged), so the
        // result is always a TaggedUnion, never a bare Kind.
        BinOp::Add => {
            let left_parts = flatten_disjoint_union(lhs);
            let right_parts = flatten_disjoint_union(rhs);
            Kind::TaggedUnion(
                left_parts
                    .into_iter()
                    .chain(right_parts)
                    .map(|p| set_kind(p, name_defs))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        // `A - B` — set difference.
        BinOp::Sub => set_kind(lhs, name_defs)?,
        // `A * B * C` — Cartesian product → tuple.
        BinOp::Mul => {
            let left_parts = flatten_domain(lhs);
            let right_parts = flatten_domain(rhs);
            Kind::Tuple(
                left_parts
                    .into_iter()
                    .chain(right_parts)
                    .map(|p| set_kind(p, name_defs))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        // `A / B` — set quotient.
        BinOp::Div => set_kind(lhs, name_defs)?,

        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Kind::Bool,
        BinOp::In | BinOp::NotIn => Kind::Bool,

        // `A | B` — union
        BinOp::Union => merge_into_union(set_kind(lhs, name_defs)?, set_kind(rhs, name_defs)?),
        // `A & B` — set intersection.
        BinOp::Intersect => set_kind(lhs, name_defs)?,
        // `A ^ B` — symmetric difference.
        BinOp::SymDiff => merge_into_union(set_kind(lhs, name_defs)?, set_kind(rhs, name_defs)?),
        BinOp::Concat => set_kind(lhs, name_defs)?,

        BinOp::And | BinOp::Or => Kind::Bool,
    })
}

fn unop_kind(un_op: &UnOp, expr: &Expr, name_defs: &NameDefs) -> Result<Kind, CompileError> {
    Ok(match &un_op {
        UnOp::Not => Kind::Bool,
        UnOp::Neg => set_kind(expr, name_defs)?,
    })
}

/// The runtime Kind of a function's return value, given its range expression.
///
/// `Fail` is the out-of-band failure sentinel and does not change the Kind of
/// the successful return values; it is stripped before inspecting the union.
/// The result drives the LLVM return-struct shape: a range of `Int | Fail`
/// compiles to `{ i1 flag, i64 value }` with `flag == 1` indicating failure.
/// Unlike plain `set_kind`, this is range-specific — a parameter can't be
/// "fallible" the same way, so `set_kind` alone is correct for domains.
pub fn range_kind(range: &Expr, name_defs: &NameDefs) -> Result<Kind, CompileError> {
    match &range.kind {
        ExprKind::Var(sym) => {
            // Bare `Fail` has its own Kind; it becomes the flag field of {Fail, Int} structs.
            if sym.0 == "Fail" {
                Ok(Kind::Fail)
            } else {
                set_kind(range, name_defs)
            }
        }
        // `A | B` — any union with a fail arm produces the fallible struct wire type {i1, i64}.
        ExprKind::BinOp {
            op: BinOp::Union,
            lhs,
            rhs,
            ..
        } => range_fail_kind(range, lhs, rhs, name_defs),
        // `A + B + C` — disjoint union; each arm retains its own kind.
        ExprKind::BinOp {
            op: BinOp::Add,
            lhs,
            rhs,
            ..
        } => range_fail_kind(range, lhs, rhs, name_defs),
        _ => set_kind(range, name_defs),
    }
}

fn is_fail_arm(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Var(sym) if sym.0 == "Fail" => true,
        ExprKind::BinOp {
            op: BinOp::Mul,
            lhs,
            ..
        } => {
            matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
        }
        _ => false,
    }
}

fn range_fail_kind(
    range: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    name_defs: &NameDefs,
) -> Result<Kind, CompileError> {
    if is_fail_arm(lhs) {
        Ok(Kind::Tuple(vec![Kind::Fail, set_kind(rhs, name_defs)?]))
    } else if is_fail_arm(rhs) {
        Ok(Kind::Tuple(vec![Kind::Fail, set_kind(lhs, name_defs)?]))
    } else {
        set_kind(range, name_defs)
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

// ── Value-position `if`/`else` branch merging ───────────────────────────────
//
// `merge_into_union`/`union_if_distinct` above are the *set-position* merge
// (domain/range unions: `A | B`, `if` in a set expression). Value-position
// `if` needs a different, LLVM-value-shaped merge — a runtime value can't be
// silently reinterpreted the way a compile-time set description can — so it
// gets its own decision function here. Both `codegen::compile_if` (which
// performs the actual LLVM coercion this describes) and the elaborator
// (which only needs the resulting Kind) call this one function, so they
// cannot silently disagree about what an `if` with mismatched branches means.

/// How two `if`/`else` branch Kinds merge into a single result Kind.
/// Mirrors `codegen::compile_if`'s coercion paths exactly; each variant here
/// corresponds 1:1 to one of its branches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IfMerge {
    /// Branches already agree — no coercion.
    Same(Kind),
    /// Either branch is the fallible `{Fail, Int}` wrapper; both become it.
    CoerceToFailStruct,
    /// Neither branch is already a TaggedUnion, and at least one is a Tuple:
    /// wrap both into a fresh 2-arm union (then = arm 0, else = arm 1).
    NewTaggedUnion { arms: Vec<Kind> },
    /// Both branches are already (different) TaggedUnions. `then`'s arms are
    /// an unchanged prefix of `merged_arms` (append-only); `else`'s tags need
    /// runtime remapping via `else_remap` (old arm index -> merged arm index).
    MergeTaggedUnions {
        merged_arms: Vec<Kind>,
        else_remap: Vec<usize>,
    },
    /// `then` is already a TaggedUnion; `else` is a single plain Kind
    /// appended as the final new arm.
    AppendElseArm { merged_arms: Vec<Kind> },
    /// `else` is already a TaggedUnion; `then` is a single plain Kind
    /// appended as the final new arm.
    AppendThenArm { merged_arms: Vec<Kind> },
    /// int-soundness-plan phase 3 step 4b: one branch is tagged `Int`, the
    /// other raw `Int64` (e.g. one arm calls a Step-A-promoted function,
    /// the other doesn't) — the raw side needs tagging before the merge;
    /// `Int` is always the canonical shared representation.
    CoerceInt64ToInt,
}

impl IfMerge {
    /// The Kind that results from this merge — all a consumer that doesn't
    /// need to build LLVM values (i.e. the elaborator) cares about.
    pub fn result_kind(&self) -> Kind {
        match self {
            IfMerge::Same(k) => k.clone(),
            IfMerge::CoerceToFailStruct => Kind::Tuple(vec![Kind::Fail, Kind::Int]),
            IfMerge::NewTaggedUnion { arms } => Kind::TaggedUnion(arms.clone()),
            IfMerge::MergeTaggedUnions { merged_arms, .. }
            | IfMerge::AppendElseArm { merged_arms }
            | IfMerge::AppendThenArm { merged_arms } => Kind::TaggedUnion(merged_arms.clone()),
            IfMerge::CoerceInt64ToInt => Kind::Int,
        }
    }
}

/// Decide how two `if`/`else` branch Kinds merge. `Err` when the branches
/// genuinely can't be reconciled (e.g. bare `Int` vs `Bool`) — codegen has no
/// coercion for this today, so this must fail loudly rather than let codegen
/// build an invalid phi from two different LLVM types.
pub fn merge_if_branches(then_ty: &Kind, else_ty: &Kind) -> Result<IfMerge, String> {
    let is_fail_struct = |k: &Kind| matches!(k, Kind::Tuple(e) if e.first() == Some(&Kind::Fail));
    if is_fail_struct(then_ty) || is_fail_struct(else_ty) {
        return Ok(IfMerge::CoerceToFailStruct);
    }
    if then_ty == else_ty {
        return Ok(IfMerge::Same(then_ty.clone()));
    }
    if matches!(
        (then_ty, else_ty),
        (Kind::Int, Kind::Int64) | (Kind::Int64, Kind::Int)
    ) {
        return Ok(IfMerge::CoerceInt64ToInt);
    }

    let then_is_tu = matches!(then_ty, Kind::TaggedUnion(_));
    let else_is_tu = matches!(else_ty, Kind::TaggedUnion(_));

    if !then_is_tu && !else_is_tu {
        if matches!(then_ty, Kind::Tuple(_)) || matches!(else_ty, Kind::Tuple(_)) {
            return Ok(IfMerge::NewTaggedUnion {
                arms: vec![then_ty.clone(), else_ty.clone()],
            });
        }
        return Err(format!(
            "if-branches with different Kinds and no Tuple/TaggedUnion side cannot be merged \
             (then={then_ty:?}, else={else_ty:?})"
        ));
    }

    match (then_ty, else_ty) {
        (Kind::TaggedUnion(then_inner), Kind::TaggedUnion(else_inner)) => {
            let mut merged = then_inner.clone();
            for arm in else_inner {
                if !merged.contains(arm) {
                    merged.push(arm.clone());
                }
            }
            let else_remap = else_inner
                .iter()
                .map(|arm| merged.iter().position(|m| m == arm).unwrap())
                .collect();
            Ok(IfMerge::MergeTaggedUnions {
                merged_arms: merged,
                else_remap,
            })
        }
        (Kind::TaggedUnion(inner), _) => {
            let mut merged = inner.clone();
            merged.push(else_ty.clone());
            Ok(IfMerge::AppendElseArm {
                merged_arms: merged,
            })
        }
        (_, Kind::TaggedUnion(inner)) => {
            let mut merged = inner.clone();
            merged.push(then_ty.clone());
            Ok(IfMerge::AppendThenArm {
                merged_arms: merged,
            })
        }
        _ => unreachable!("then_is_tu || else_is_tu guarantees at least one TaggedUnion branch"),
    }
}

// ── `++` tuple-to-vector coercion ────────────────────────────────────────────

/// Which side (if either) of a `lhs ++ rhs` needs its literal Tuple coerced
/// into a Vector before the runtime concat call. Mirrors
/// `codegen::compile_vec_concat`'s coercion exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcatMerge {
    /// Both sides are already `Vector` — no coercion.
    Same,
    /// `lhs` is a `Tuple`; coerce it into a `Vector` matching `rhs`'s element kind.
    CoerceLhsToVector,
    /// `rhs` is a `Tuple`; coerce it into a `Vector` matching `lhs`'s element kind.
    CoerceRhsToVector,
}

/// Decide how `lhs ++ rhs` merges, and the resulting (always-`Vector`) Kind.
/// `Err` when neither side is a `Vector` to coerce the other towards.
pub fn merge_concat_kinds(lhs: &Kind, rhs: &Kind) -> Result<(ConcatMerge, Kind), String> {
    match (lhs, rhs) {
        (Kind::Vector(ek), Kind::Vector(_)) => Ok((ConcatMerge::Same, Kind::Vector(ek.clone()))),
        (Kind::Tuple(_), Kind::Vector(ek)) => {
            Ok((ConcatMerge::CoerceLhsToVector, Kind::Vector(ek.clone())))
        }
        (Kind::Vector(ek), Kind::Tuple(_)) => {
            Ok((ConcatMerge::CoerceRhsToVector, Kind::Vector(ek.clone())))
        }
        _ => Err(format!(
            "`++` requires vector (X*) operands, got {lhs:?} ++ {rhs:?}"
        )),
    }
}
