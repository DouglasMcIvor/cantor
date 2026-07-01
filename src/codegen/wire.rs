//! LLVM wire-type helpers — functions that decide how Cantor values are
//! represented in LLVM IR.
//!
//! These sit one layer above `Kind` (the abstract domain classifier): they map
//! set expressions and signatures to the concrete struct shapes emitted by the
//! code generator.  Nothing here calls inkwell directly; the LLVM-specific
//! calls live in `codegen/mod.rs` (kind_to_llvm_type, declare_function, etc.).

use crate::{
    ast::{FunctionSig, NameDefs, param_set_exprs},
    kind::{Kind, set_kind},
};

pub use crate::kind::range_kind;

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
