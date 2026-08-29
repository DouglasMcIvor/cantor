//! Semantic analysis layer, built on top of the parsed AST.
//!
//! `builtins` is the canonical registry of built-in named sets (`Int`, `Nat`,
//! `Bool`, `Int8`, …) — the single place their `Kind` and value-bound are
//! recorded, consulted by `kind.rs`, the solver, and codegen so each backend
//! doesn't independently re-encode "Nat means x >= 0".
//!
//! `elaborate`/`tree` implement the elaboration pass (AST → SemanticTree)
//! described in `kind.rs`'s top-of-file TODO.

pub mod builtins;
pub mod elaborate;
pub mod tree;
mod tree_collect;
mod wellfounded;
