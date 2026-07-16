//! Arena deep-copy of a flattened `State` value (see `arena.rs`'s module doc
//! and `event_loop::drive_event_loop`, which is the only caller).
//!
//! `LeafShape`/`VectorElemShape`/`SetBacking` describe, for one leaf of a
//! flattened `State` (mirroring `codegen::wire::leaf_count`'s recursive
//! structure) or one `Vector` element, whether the raw i64 word is a plain
//! scalar (copy through unchanged) or a pointer into the arena that must be
//! recreated in whatever arena is current before the old one is dropped.
//! Built by the compiler from `Kind` — this crate deliberately has no `Kind`
//! dependency (see `lib.rs`'s module doc on keeping AOT binaries free of
//! compiler internals), so these are a minimal purpose-built descriptor
//! instead, constructed once per compiled event-loop program by
//! `codegen::wire::state_leaf_shape` and hard-coded as a literal into the
//! AOT driver's generated source (`codegen::aot`) or built in-process for
//! the JIT path (`main.rs::run_event_loop`).
//!
//! Scope (deliberately narrower than every `Kind` shape the language
//! otherwise supports — each gap below is rejected with a `CompileError` at
//! `state_leaf_shape`, never silently mishandled here):
//!   - `Vector(Tuple(_))` (struct vectors) is not supported: whether an
//!     `Int` tuple field is stored tagged or raw is genuinely ambiguous from
//!     `codegen/expr_vec.rs`'s current struct-vec push path (unlike the
//!     direct `Vector(Int)` case, it does not call `ensure_raw_int64_container`),
//!     and guessing wrong here would mean dereferencing an arbitrary odd
//!     integer as a `CantorBigInt` pointer.
//!   - `TaggedUnion` anywhere is not supported — mirrors the pre-existing
//!     gap in `codegen::trampoline` (`TaggedUnion input/output not yet
//!     supported`), so this introduces no new restriction.

use crate::bigint::{CantorTaggedIntSet, deep_copy_tagged_int};
use crate::{CantorBoolSet, CantorIntSet, CantorListVec, CantorVecBool, CantorVecI64, arena};

use arrow_array::builder::Int64Builder;

/// Which concrete runtime type backs a `Kind::Set(_)` — see
/// `codegen/expr.rs`'s set-literal dispatch, which this mirrors exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SetBacking {
    /// `Kind::Set(Kind::Int)` under whole-program BigInt tagging —
    /// `CantorTaggedIntSet`; elements may themselves be boxed.
    TaggedInt,
    /// `Kind::Set(Kind::Int64)` (always raw) — `CantorIntSet`.
    PlainInt,
    /// `Kind::Set(Kind::Bool)` or `Kind::Set(Kind::Fail)` — `CantorBoolSet`.
    PlainBool,
}

/// The shape of one `Vector(elem)` element — recursive only through
/// `Nested`, since `Vector(Tuple(_))`/`Vector(TaggedUnion(_))` are rejected
/// at `state_leaf_shape` before a `VectorElemShape` needing them could exist.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VectorElemShape {
    /// Flat Arrow-backed elements with no nested arena pointers to chase
    /// (`Int`, `Int64`, `Char`, or `Bool` — the first three all use the raw
    /// `_i64` Arrow family per `codegen/expr_vec.rs`'s `vec_builder_fns`;
    /// `Vector(Int)` storage in particular is *always* raw, never boxed, by
    /// design — see that file's `compile_vector_elem_get` comment). Deep
    /// copy is a cheap Arc-bump clone of the whole Arrow array.
    FlatScalar { bool_backed: bool },
    /// `Vector(Vector(_))` (or deeper) — each element is itself a pointer to
    /// an inner vector object that must be recursively deep-copied.
    Nested(Box<VectorElemShape>),
}

/// The shape of one flattened `State` leaf (or a whole `State`, via `Tuple`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeafShape {
    /// Copy the raw i64 through unchanged — never a pointer into the arena
    /// (`Bool`, `Int64`, `Fail`, `None`, `Signed32`, `Unsigned32`, `Char`).
    Scalar,
    /// `Kind::Int` under whole-program BigInt tagging (unconditionally true
    /// for every event-loop program — both `cantor run` and `cantor build`
    /// compile through `compile_constrained`, which always activates
    /// tagging; see `codegen::wire::state_leaf_shape`'s doc comment): the
    /// word may or may not be a low-bit-tagged pointer to a `CantorBigInt`.
    TaggedInt,
    /// `Kind::Set(elem)`.
    Set(SetBacking),
    /// `Kind::Vector(elem)`.
    Vector(VectorElemShape),
    /// `Kind::Tuple(elems)` — recurse leaf-by-leaf, exactly mirroring
    /// `codegen::wire::leaf_count`'s own recursion so leaf positions line up
    /// with the flattened buffer `event_loop::drive_event_loop` reads from.
    Tuple(Vec<LeafShape>),
}

/// Deep-copy every leaf of a flattened `State` value into whatever arena is
/// currently installed (see `arena::swap`), returning the new leaf buffer.
/// `leaves.len()` must equal the leaf count `shape` describes.
pub fn deep_copy_leaves(shape: &LeafShape, leaves: &[i64]) -> Vec<i64> {
    let mut out = Vec::with_capacity(leaves.len());
    let mut idx = 0usize;
    copy_into(shape, leaves, &mut idx, &mut out);
    debug_assert_eq!(
        idx,
        leaves.len(),
        "deep_copy_leaves: shape's leaf count doesn't match the buffer length"
    );
    out
}

fn copy_into(shape: &LeafShape, leaves: &[i64], idx: &mut usize, out: &mut Vec<i64>) {
    if let LeafShape::Tuple(elems) = shape {
        for elem in elems {
            copy_into(elem, leaves, idx, out);
        }
        return;
    }
    let word = leaves[*idx];
    *idx += 1;
    out.push(copy_leaf(shape, word));
}

fn copy_leaf(shape: &LeafShape, word: i64) -> i64 {
    match shape {
        LeafShape::Scalar => word,
        LeafShape::TaggedInt => deep_copy_tagged_int(word),
        LeafShape::Set(backing) => copy_set(*backing, word),
        LeafShape::Vector(vshape) => copy_vector(vshape, word),
        LeafShape::Tuple(_) => unreachable!("Tuple is handled by copy_into, not copy_leaf"),
    }
}

fn copy_set(backing: SetBacking, ptr: i64) -> i64 {
    match backing {
        SetBacking::PlainInt => {
            let s = unsafe { &*(ptr as *const CantorIntSet) };
            arena::alloc(s.clone())
        }
        SetBacking::PlainBool => {
            let s = unsafe { &*(ptr as *const CantorBoolSet) };
            arena::alloc(s.clone())
        }
        SetBacking::TaggedInt => {
            let s = unsafe { &*(ptr as *const CantorTaggedIntSet) };
            arena::alloc(s.arena_deep_copy())
        }
    }
}

fn copy_vector(shape: &VectorElemShape, ptr: i64) -> i64 {
    match shape {
        VectorElemShape::FlatScalar { bool_backed: false } => {
            let v = unsafe { &*(ptr as *const CantorVecI64) };
            arena::alloc(v.clone())
        }
        VectorElemShape::FlatScalar { bool_backed: true } => {
            let v = unsafe { &*(ptr as *const CantorVecBool) };
            arena::alloc(v.clone())
        }
        VectorElemShape::Nested(inner) => {
            let v = unsafe { &*(ptr as *const CantorListVec) };
            let mut builder = Int64Builder::with_capacity(v.elems.len());
            for i in 0..v.elems.len() {
                let elem_ptr = v.elems.value(i);
                builder.append_value(copy_vector(inner, elem_ptr));
            }
            arena::alloc(CantorListVec {
                elems: builder.finish(),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_and_tagged_int_pass_through_or_rebox() {
        // A tagged small int is shifted left by 1 (low bit 0) — see
        // `bigint.rs`'s tagging scheme doc comment; `14` here tags the
        // value 7, not the raw word 7 (which would misread as boxed, since
        // it's odd).
        let leaves = [42i64, 14i64];
        let shape = LeafShape::Tuple(vec![LeafShape::Scalar, LeafShape::TaggedInt]);
        let out = deep_copy_leaves(&shape, &leaves);
        assert_eq!(out, vec![42, 14]);
        arena::reset();
    }

    #[test]
    fn boxed_bigint_survives_a_reset() {
        // Outside the tagged small-int range, so `cantor_bigint_from_i64`
        // boxes it — exercises the re-box (not passthrough) branch of
        // `deep_copy_tagged_int`.
        let word = crate::bigint::cantor_bigint_from_i64(crate::bigint::TAG_SMALL_MAX + 1);
        assert_eq!(
            word & 1,
            1,
            "value must actually be boxed for this test to mean anything"
        );

        let old = arena::swap(arena::Arena::new());
        let copied = deep_copy_leaves(&LeafShape::TaggedInt, &[word]);
        // `word` (a pointer into `old`) must not be read after this point.
        drop(old);

        assert_ne!(
            copied[0], word,
            "must be a distinct allocation, not the same pointer"
        );
        assert_eq!(
            crate::bigint::cantor_bigint_to_i64(copied[0]),
            crate::bigint::TAG_SMALL_MAX + 1
        );
        arena::reset();
    }

    #[test]
    fn plain_set_survives_a_reset() {
        let ptr = crate::cantor_set_new_i64();
        crate::cantor_set_insert_i64(ptr, 1);
        crate::cantor_set_insert_i64(ptr, 2);

        let old = arena::swap(arena::Arena::new());
        let copied = deep_copy_leaves(&LeafShape::Set(SetBacking::PlainInt), &[ptr]);
        drop(old);

        let new_ptr = copied[0];
        assert_eq!(crate::cantor_set_size_i64(new_ptr), 2);
        assert_eq!(crate::cantor_set_contains_i64(new_ptr, 1), 1);
        assert_eq!(crate::cantor_set_contains_i64(new_ptr, 2), 1);
        arena::reset();
    }

    #[test]
    fn flat_vector_survives_a_reset() {
        let b = crate::cantor_vec_builder_new_i64();
        crate::cantor_vec_builder_push_i64(b, 10);
        crate::cantor_vec_builder_push_i64(b, 20);
        let ptr = crate::cantor_vec_builder_finish_i64(b);

        let old = arena::swap(arena::Arena::new());
        let shape = LeafShape::Vector(VectorElemShape::FlatScalar { bool_backed: false });
        let copied = deep_copy_leaves(&shape, &[ptr]);
        drop(old);

        let new_ptr = copied[0];
        assert_eq!(crate::cantor_vec_len_i64(new_ptr), 2);
        assert_eq!(crate::cantor_vec_get_i64(new_ptr, 0), 10);
        assert_eq!(crate::cantor_vec_get_i64(new_ptr, 1), 20);
        arena::reset();
    }

    #[test]
    fn nested_vector_survives_a_reset() {
        // Build Vector(Vector(Int)): [[1, 2], [3]]
        let inner_a_b = crate::cantor_vec_builder_new_i64();
        crate::cantor_vec_builder_push_i64(inner_a_b, 1);
        crate::cantor_vec_builder_push_i64(inner_a_b, 2);
        let inner_a = crate::cantor_vec_builder_finish_i64(inner_a_b);

        let inner_b_b = crate::cantor_vec_builder_new_i64();
        crate::cantor_vec_builder_push_i64(inner_b_b, 3);
        let inner_b = crate::cantor_vec_builder_finish_i64(inner_b_b);

        let outer_b = crate::cantor_list_vec_builder_new();
        crate::cantor_list_vec_builder_push(outer_b, inner_a);
        crate::cantor_list_vec_builder_push(outer_b, inner_b);
        let outer = crate::cantor_list_vec_builder_finish(outer_b);

        let old = arena::swap(arena::Arena::new());
        let shape = LeafShape::Vector(VectorElemShape::Nested(Box::new(
            VectorElemShape::FlatScalar { bool_backed: false },
        )));
        let copied = deep_copy_leaves(&shape, &[outer]);
        drop(old); // frees the original outer + inner vectors

        let new_outer = copied[0];
        assert_eq!(crate::cantor_list_vec_len(new_outer), 2);
        let new_inner_a = crate::cantor_list_vec_get(new_outer, 0);
        let new_inner_b = crate::cantor_list_vec_get(new_outer, 1);
        assert_eq!(crate::cantor_vec_len_i64(new_inner_a), 2);
        assert_eq!(crate::cantor_vec_get_i64(new_inner_a, 0), 1);
        assert_eq!(crate::cantor_vec_get_i64(new_inner_a, 1), 2);
        assert_eq!(crate::cantor_vec_len_i64(new_inner_b), 1);
        assert_eq!(crate::cantor_vec_get_i64(new_inner_b, 0), 3);
        arena::reset();
    }
}
