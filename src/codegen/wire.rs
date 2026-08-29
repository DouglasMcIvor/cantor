//! LLVM wire-type helpers — functions that decide how Cantor values are
//! represented in LLVM IR.
//!
//! These sit one layer above `Kind` (the abstract domain classifier): they map
//! set expressions and signatures to the concrete struct shapes emitted by the
//! code generator.  Nothing here calls inkwell directly; the LLVM-specific
//! calls live in `codegen/mod.rs` (kind_to_llvm_type, declare_function, etc.).

use crate::error::CompileError;
use crate::kind::Kind;
use crate::runtime::deep_copy::{LeafShape, SetBacking, VectorElemShape};
use crate::span::Span;

pub use crate::kind::range_kind;

/// Number of i64 leaf fields when a Kind is serialised into a tagged-union payload.
/// Bool and Int each occupy one slot; Tuple recurses into its element kinds.
pub fn leaf_count(kind: &Kind) -> usize {
    match kind {
        Kind::Bool | Kind::Int | Kind::Int64 | Kind::Set(_) | Kind::Fail | Kind::None => 1,
        // Rational is an i64 pointer to a boxed BigRational — one leaf, so
        // adding it changes no wire shape anywhere.
        Kind::Rational => 1,
        // Signed32/Unsigned32/Char cross the ABI boundary widened to i64
        // (sext/zext respectively), same convention as Bool's i1<->i64 —
        // one leaf each.
        Kind::Signed32 | Kind::Unsigned32 | Kind::Char => 1,
        Kind::Tuple(elems) => elems.iter().map(leaf_count).sum(),
        Kind::TaggedUnion(arms) => 1 + tagged_union_leaf_count(arms),
        // Vector is an i64 pointer (like Set) — one leaf.
        Kind::Vector(_) => 1,
        // TODO(float32): codegen step — almost certainly 1 (widened into an
        // i64 leaf like Signed32/Unsigned32/Char), but that ABI choice isn't
        // decided/tested yet, so this stays a loud gap rather than a guess.
        Kind::Float32 => crate::kind::float32_unreachable(),
    }
}

/// Maximum leaf count over all arms; gives the payload width of the tagged-union struct.
pub fn tagged_union_leaf_count(arms: &[Kind]) -> usize {
    arms.iter().map(leaf_count).max().unwrap_or(0)
}

/// True when a Kind is exactly `Char*` (`Vector(Char)`).
fn is_char_star(kind: &Kind) -> bool {
    matches!(kind, Kind::Vector(elem) if **elem == Kind::Char)
}

/// True when `(param_kinds, return_kind)` matches the IO event loop's shape
/// `Char* * S -> Output * S` (docs/design-decisions.md §6) — 2 params, first
/// param `Char*` (Event, still fixed for v0), 2-element tuple return. Output
/// (the first return element) is *not* Kind-checked here any more — it used
/// to be pinned to `Char*` too, but codegen can now marshal more than
/// strings across the event-loop boundary; `classify_output_shape` below
/// decides which specific Output Kinds are actually usable, which build
/// targets support them, and error out clearly if it recognizes neither.
/// Kind-only: the (stronger) identifier-equality checks on `S` already
/// happened in `solver::event_loop::validate_event_loop_main` before a
/// `ConstrainedTree` exposing this shape could exist at all.
///
/// Shared by `compile.rs` (decides which trampolines to emit), `main.rs`
/// (JIT event-loop dispatch), and `aot.rs` (AOT event-loop dispatch) — one
/// definition of the shape instead of three copies drifting apart.
pub fn is_event_loop_step_shape(param_kinds: &[Kind], return_kind: &Kind) -> bool {
    param_kinds.len() == 2
        && is_char_star(&param_kinds[0])
        && matches!(return_kind, Kind::Tuple(elems) if elems.len() == 2)
}

/// Which Output Kind an event-loop `main` uses, among the ones codegen
/// actually knows how to marshal — `None` for anything else (an
/// `Unsupported` error at the call site, not a silent fallback, per this
/// codebase's rule that unimplemented paths must fail loudly).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputShape {
    /// The original MVP shape: `Output` is `Char*`, printed as a line of
    /// text. Supported by every target (native `cantor run`/`cantor build`,
    /// and `--target wasm32`).
    CharStar,
    /// `Nat * Nat * Vector(Unsigned32)` — width, height, row-major pixels
    /// packed one `0xRRGGBBAA` per element. A *convention*, not a new
    /// builtin Kind (docs/design-decisions.md §6) — deliberately just a
    /// Tuple/Vector/Unsigned32 shape the language already had, recognized
    /// structurally here. `--target wasm32`-only: there is no way to render
    /// an image over `cantor run`'s stdin/stdout loop.
    Image,
}

/// Classify an event-loop `main`'s Output Kind (the event-loop return
/// tuple's first element), or `None` if codegen doesn't know how to marshal
/// it at all yet.
pub fn classify_output_shape(kind: &Kind) -> Option<OutputShape> {
    if is_char_star(kind) {
        return Some(OutputShape::CharStar);
    }
    let Kind::Tuple(elems) = kind else {
        return None;
    };
    let [width, height, pixels] = elems.as_slice() else {
        return None;
    };
    let is_pixel_vector = matches!(pixels, Kind::Vector(elem) if **elem == Kind::Unsigned32);
    if *width == Kind::Int && *height == Kind::Int && is_pixel_vector {
        Some(OutputShape::Image)
    } else {
        None
    }
}

/// Convert a `State` `Kind` into the deep-copy shape descriptor
/// `cantor_runtime::event_loop::drive_event_loop` uses at the arena-reset
/// boundary (see the arena memory plan: `arena.rs`'s module doc,
/// `deep_copy.rs`'s module doc). Every event-loop program — both `cantor
/// run` and `cantor build` — compiles through `compile_constrained`, which
/// always passes `overflow_ctx = Some(..)`, so `Compiler::tagging_active()`
/// is unconditionally `true` here; `Kind::Int` therefore always maps to
/// `LeafShape::TaggedInt`, never the plain-raw case a non-event-loop
/// pipeline would need.
///
/// `span` is used only for the error case — the caller doesn't have a
/// specific sub-expression to blame (State is a single named set), so this
/// takes whatever span best identifies the event-loop `main` as a whole.
pub fn state_leaf_shape(kind: &Kind, span: Span) -> Result<LeafShape, CompileError> {
    Ok(match kind {
        Kind::Bool
        | Kind::Int64
        | Kind::Fail
        | Kind::None
        | Kind::Signed32
        | Kind::Unsigned32
        | Kind::Char => LeafShape::Scalar,
        Kind::Int => LeafShape::TaggedInt,
        Kind::Set(elem) => LeafShape::Set(match elem.as_ref() {
            Kind::Int => SetBacking::TaggedInt,
            Kind::Int64 => SetBacking::PlainInt,
            Kind::Bool | Kind::Fail => SetBacking::PlainBool,
            other => {
                return Err(CompileError::Unsupported {
                    feature: format!(
                        "event-loop State containing Set({other:?}) — arena deep-copy \
                         doesn't support this Set element kind yet"
                    ),
                    span,
                });
            }
        }),
        Kind::Vector(elem) => LeafShape::Vector(vector_elem_shape(elem, span)?),
        Kind::Tuple(elems) => LeafShape::Tuple(
            elems
                .iter()
                .map(|k| state_leaf_shape(k, span))
                .collect::<Result<_, _>>()?,
        ),
        Kind::TaggedUnion(_) => {
            return Err(CompileError::Unsupported {
                feature: "event-loop State containing a TaggedUnion — arena deep-copy \
                          doesn't support this yet (mirrors the same gap in \
                          `codegen::trampoline`'s wire (de)serialization)"
                    .to_string(),
                span,
            });
        }
        // A boxed `Rational` lives in the arena, so surviving an arena reset
        // needs the same deep-copy entry point `CantorBigInt` has. Deferred
        // rather than approximated — see docs/rational-plan.md stage 3.
        Kind::Rational => {
            return Err(CompileError::Unsupported {
                feature: "event-loop State containing a Rational — arena deep-copy \
                          doesn't support boxed rationals yet"
                    .to_string(),
                span,
            });
        }
        Kind::Float32 => {
            return Err(CompileError::Unsupported {
                feature: "event-loop State containing a Float32 — Float32 codegen \
                          isn't implemented yet"
                    .to_string(),
                span,
            });
        }
    })
}

/// `Vector(elem)`'s deep-copy shape — see `deep_copy.rs`'s module doc for
/// why `Tuple`/`TaggedUnion` elements are rejected rather than supported.
fn vector_elem_shape(elem: &Kind, span: Span) -> Result<VectorElemShape, CompileError> {
    Ok(match elem {
        Kind::Int | Kind::Char | Kind::Signed32 | Kind::Unsigned32 => {
            VectorElemShape::FlatScalar { bool_backed: false }
        }
        Kind::Bool => VectorElemShape::FlatScalar { bool_backed: true },
        Kind::Vector(inner) => VectorElemShape::Nested(Box::new(vector_elem_shape(inner, span)?)),
        other => {
            return Err(CompileError::Unsupported {
                feature: format!(
                    "event-loop State containing Vector({other:?}) — arena deep-copy \
                     doesn't support this Vector element kind yet"
                ),
                span,
            });
        }
    })
}
