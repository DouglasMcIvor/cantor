//! LLVM wire-type helpers — functions that decide how Cantor values are
//! represented in LLVM IR.
//!
//! These sit one layer above `Kind` (the abstract domain classifier): they map
//! set expressions and signatures to the concrete struct shapes emitted by the
//! code generator.  Nothing here calls inkwell directly; the LLVM-specific
//! calls live in `codegen/mod.rs` (kind_to_llvm_type, declare_function, etc.).

use crate::kind::Kind;

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
