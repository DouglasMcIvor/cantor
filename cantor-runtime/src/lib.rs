//! Cantor runtime library — called from JIT-compiled code via extern "C" ABI.
//!
//! All pointer arguments cross the ABI boundary as i64 (pointer-as-i64),
//! matching the compiler's uniform i64 calling convention.
//!
//! Memory: sets, vectors, and BigInts are heap-allocated through the `arena`
//! module (see `arena.rs`), which registers each allocation for a deferred
//! drop instead of leaking it via `Box::into_raw`. Nothing calls
//! `arena::reset()` yet, so in practice allocations still live for the
//! whole program's lifetime — TODO: wire `reset()` into the event-loop step
//! boundary together with a root-preserving deep copy of `State` (see
//! `event_loop.rs`).

use std::sync::Arc;

use arrow_array::{
    Array, ArrayRef, BooleanArray, Int64Array, StructArray, UnionArray,
    builder::{ArrayBuilder, BooleanBuilder, Int64Builder, StructBuilder},
};
use arrow_buffer::ScalarBuffer;
use arrow_schema::{DataType, Field, Fields, UnionFields};

// ── Int set ───────────────────────────────────────────────────────────────────

/// A finite set of i64 values, stored sorted for O(log n) membership testing.
///
/// `Clone` is a plain `Vec` clone — safe for arena deep-copy (`deep_copy.rs`)
/// because elements are always raw i64s, never pointers into the arena.
#[derive(Default, Clone)]
pub struct CantorIntSet {
    elements: Vec<i64>,
}

impl CantorIntSet {
    pub fn insert(&mut self, val: i64) {
        match self.elements.binary_search(&val) {
            Ok(_) => {}
            Err(pos) => self.elements.insert(pos, val),
        }
    }

    pub fn contains(&self, val: i64) -> bool {
        self.elements.binary_search(&val).is_ok()
    }

    pub fn size(&self) -> i64 {
        self.elements.len() as i64
    }

    pub fn get(&self, idx: i64) -> i64 {
        self.elements[idx as usize]
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_new_i64() -> i64 {
    crate::arena::alloc(CantorIntSet::default())
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_insert_i64(set: i64, val: i64) {
    unsafe { &mut *(set as *mut CantorIntSet) }.insert(val);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_contains_i64(set: i64, val: i64) -> i64 {
    unsafe { &*(set as *const CantorIntSet) }.contains(val) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_size_i64(set: i64) -> i64 {
    unsafe { &*(set as *const CantorIntSet) }.size()
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_get_i64(set: i64, idx: i64) -> i64 {
    unsafe { &*(set as *const CantorIntSet) }.get(idx)
}

// ── Bool set ──────────────────────────────────────────────────────────────────

/// A finite set of bool values. At most two elements; stored sorted (false < true).
///
/// The ABI passes booleans as i64 (0 = false, non-zero = true) to match the
/// compiler's uniform calling convention.
///
/// `Clone` is a plain `Vec` clone — safe for arena deep-copy (`deep_copy.rs`)
/// since elements are never pointers into the arena.
#[derive(Default, Clone)]
pub struct CantorBoolSet {
    elements: Vec<bool>,
}

impl CantorBoolSet {
    pub fn insert(&mut self, val: bool) {
        // bool: Ord with false < true, so binary_search gives the correct sorted position.
        match self.elements.binary_search(&val) {
            Ok(_) => {}
            Err(pos) => self.elements.insert(pos, val),
        }
    }

    pub fn contains(&self, val: bool) -> bool {
        self.elements.binary_search(&val).is_ok()
    }

    pub fn size(&self) -> i64 {
        self.elements.len() as i64
    }

    /// Returns the element at `idx` as i64 (0 or 1).
    pub fn get(&self, idx: i64) -> i64 {
        self.elements[idx as usize] as i64
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_new_bool() -> i64 {
    crate::arena::alloc(CantorBoolSet::default())
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_insert_bool(set: i64, val: i64) {
    unsafe { &mut *(set as *mut CantorBoolSet) }.insert(val != 0);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_contains_bool(set: i64, val: i64) -> i64 {
    unsafe { &*(set as *const CantorBoolSet) }.contains(val != 0) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_size_bool(set: i64) -> i64 {
    unsafe { &*(set as *const CantorBoolSet) }.size()
}

/// Returns the element at `idx` as i64 (0 or 1).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_set_get_bool(set: i64, idx: i64) -> i64 {
    unsafe { &*(set as *const CantorBoolSet) }.get(idx)
}

// ── Int vector (Kind::Vector(Kind::Int)) ─────────────────────────────────────
//
// Backed by Apache Arrow `Int64Array` (immutable, columnar).
// Construction uses `CantorVecBuilderI64` (wraps `Int64Builder`) which is
// allocated, populated, and then "finished" into a frozen `CantorVecI64`.
// "Mutation" at the Cantor level means rebinding a variable to a new vector;
// `cantor_vec_push_i64` provides a purely functional append that returns a new
// pointer while leaving the old vector intact.

pub struct CantorVecBuilderI64 {
    builder: Int64Builder,
}

/// `Clone` is a cheap Arc-bump of the underlying Arrow buffer (Arrow arrays
/// are internally reference-counted), not a data copy — arena deep-copy
/// (`deep_copy.rs`) relies on this: cloning into a new arena's wrapper keeps
/// the buffer alive independent of which arena gets dropped first.
#[derive(Clone)]
pub struct CantorVecI64 {
    array: Int64Array,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_new_i64() -> i64 {
    crate::arena::alloc(CantorVecBuilderI64 {
        builder: Int64Builder::new(),
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_push_i64(builder: i64, val: i64) {
    unsafe { &mut *(builder as *mut CantorVecBuilderI64) }
        .builder
        .append_value(val);
}

/// Freeze the builder into a `CantorVecI64`. The builder is left alive in
/// the arena (not freed here) — arena semantics reclaim it later.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_finish_i64(builder: i64) -> i64 {
    let b = unsafe { &mut *(builder as *mut CantorVecBuilderI64) };
    let array = b.builder.finish();
    crate::arena::alloc(CantorVecI64 { array })
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_len_i64(vec: i64) -> i64 {
    unsafe { &*(vec as *const CantorVecI64) }.array.len() as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_get_i64(vec: i64, idx: i64) -> i64 {
    unsafe { &*(vec as *const CantorVecI64) }
        .array
        .value(idx as usize)
}

/// Purely functional append: returns a new vector with `val` appended.
/// The old vector is NOT freed (consistent with the arena-free design).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_push_i64(vec: i64, val: i64) -> i64 {
    let old = unsafe { &*(vec as *const CantorVecI64) };
    let mut builder = Int64Builder::with_capacity(old.array.len() + 1);
    for i in 0..old.array.len() {
        builder.append_value(old.array.value(i));
    }
    builder.append_value(val);
    crate::arena::alloc(CantorVecI64 {
        array: builder.finish(),
    })
}

// ── Bool vector (Kind::Vector(Kind::Bool)) ────────────────────────────────────
//
// Same design as the Int vector but backed by `BooleanArray`.
// ABI passes booleans as i64 (0 = false, non-zero = true).

pub struct CantorVecBuilderBool {
    builder: BooleanBuilder,
}

/// `Clone` is a cheap Arc-bump of the underlying Arrow buffer — see
/// `CantorVecI64`'s doc comment; same reasoning applies here.
#[derive(Clone)]
pub struct CantorVecBool {
    array: BooleanArray,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_new_bool() -> i64 {
    crate::arena::alloc(CantorVecBuilderBool {
        builder: BooleanBuilder::new(),
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_push_bool(builder: i64, val: i64) {
    unsafe { &mut *(builder as *mut CantorVecBuilderBool) }
        .builder
        .append_value(val != 0);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_finish_bool(builder: i64) -> i64 {
    let b = unsafe { &mut *(builder as *mut CantorVecBuilderBool) };
    let array = b.builder.finish();
    crate::arena::alloc(CantorVecBool { array })
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_len_bool(vec: i64) -> i64 {
    unsafe { &*(vec as *const CantorVecBool) }.array.len() as i64
}

/// Returns the element at `idx` as i64 (0 or 1).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_get_bool(vec: i64, idx: i64) -> i64 {
    unsafe { &*(vec as *const CantorVecBool) }
        .array
        .value(idx as usize) as i64
}

/// Purely functional append for Bool vectors.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_push_bool(vec: i64, val: i64) -> i64 {
    let old = unsafe { &*(vec as *const CantorVecBool) };
    let mut builder = BooleanBuilder::with_capacity(old.array.len() + 1);
    for i in 0..old.array.len() {
        builder.append_value(old.array.value(i));
    }
    builder.append_value(val != 0);
    crate::arena::alloc(CantorVecBool {
        array: builder.finish(),
    })
}

// ── Vector concatenation ──────────────────────────────────────────────────────

/// Concatenate two Int* vectors into a new one.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_concat_i64(a: i64, b: i64) -> i64 {
    let va = unsafe { &*(a as *const CantorVecI64) };
    let vb = unsafe { &*(b as *const CantorVecI64) };
    let mut builder = Int64Builder::with_capacity(va.array.len() + vb.array.len());
    for i in 0..va.array.len() {
        builder.append_value(va.array.value(i));
    }
    for i in 0..vb.array.len() {
        builder.append_value(vb.array.value(i));
    }
    crate::arena::alloc(CantorVecI64 {
        array: builder.finish(),
    })
}

/// Concatenate two Bool* vectors into a new one.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_concat_bool(a: i64, b: i64) -> i64 {
    let va = unsafe { &*(a as *const CantorVecBool) };
    let vb = unsafe { &*(b as *const CantorVecBool) };
    let mut builder = BooleanBuilder::with_capacity(va.array.len() + vb.array.len());
    for i in 0..va.array.len() {
        builder.append_value(va.array.value(i));
    }
    for i in 0..vb.array.len() {
        builder.append_value(vb.array.value(i));
    }
    crate::arena::alloc(CantorVecBool {
        array: builder.finish(),
    })
}

// ── Struct vectors ((A * B)*) ────────────────────────────────────────────────
//
// Kind::Vector(Kind::Tuple(field_kinds)) is backed by a CantorStructVec:
// an Apache Arrow StructArray with one column per field.  All values are
// stored as i64 (Bool fields widened to 0/1 by codegen; vector fields stored
// as i64 pointers).  The field names are "f0", "f1", … (opaque internal detail).
//
// ABI contract: codegen calls push_field for each field of each row in order
// (field 0 first, then field 1, …), then finish. The field count (n_fields) is
// supplied at builder_new time and stored in the struct.

pub struct CantorStructVec {
    array: StructArray,
}

pub struct CantorStructVecBuilder {
    n_fields: usize,
    builder: StructBuilder,
}

fn make_struct_builder(n: usize) -> StructBuilder {
    let fields: Fields = (0..n)
        .map(|i| Arc::new(Field::new(format!("f{i}"), DataType::Int64, false)))
        .collect::<Vec<_>>()
        .into();
    let field_builders: Vec<Box<dyn ArrayBuilder>> = (0..n)
        .map(|_| Box::new(Int64Builder::new()) as Box<dyn ArrayBuilder>)
        .collect();
    StructBuilder::new(fields, field_builders)
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_builder_new(n_fields: i64) -> i64 {
    let n = n_fields as usize;
    crate::arena::alloc(CantorStructVecBuilder {
        n_fields: n,
        builder: make_struct_builder(n),
    })
}

/// Append `value` to column `field_idx` of the current row.
/// Bool values are already widened to 0/1 i64 by the codegen.
/// Calls `builder.append(true)` after the last field to commit the row.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_builder_push_field(builder: i64, field_idx: i64, value: i64) {
    let b = unsafe { &mut *(builder as *mut CantorStructVecBuilder) };
    let idx = field_idx as usize;
    b.builder
        .field_builder::<Int64Builder>(idx)
        .unwrap()
        .append_value(value);
    if idx == b.n_fields - 1 {
        b.builder.append(true);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_builder_finish(builder: i64) -> i64 {
    let b = unsafe { &mut *(builder as *mut CantorStructVecBuilder) };
    let array = b.builder.finish();
    crate::arena::alloc(CantorStructVec { array })
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_len(vec: i64) -> i64 {
    unsafe { &*(vec as *const CantorStructVec) }.array.len() as i64
}

/// Returns the i64 value stored in field `field_idx` of row `row_idx`.
/// Bool fields are returned as 0 or 1; codegen truncates to i1.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_get_field(vec: i64, row_idx: i64, field_idx: i64) -> i64 {
    let v = unsafe { &*(vec as *const CantorStructVec) };
    v.array
        .column(field_idx as usize)
        .as_any()
        .downcast_ref::<Int64Array>()
        .expect("struct field must be Int64Array")
        .value(row_idx as usize)
}

/// Concatenate two struct vectors of the same shape.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_concat(a: i64, b: i64) -> i64 {
    let va = unsafe { &*(a as *const CantorStructVec) };
    let vb = unsafe { &*(b as *const CantorStructVec) };
    let n = va.array.num_columns();
    assert_eq!(
        n,
        vb.array.num_columns(),
        "cantor_struct_vec_concat: field count mismatch"
    );
    let mut sb = make_struct_builder(n);
    for sv in [&va.array, &vb.array] {
        for row in 0..sv.len() {
            for col in 0..n {
                let val = sv
                    .column(col)
                    .as_any()
                    .downcast_ref::<Int64Array>()
                    .expect("struct col must be Int64Array")
                    .value(row);
                sb.field_builder::<Int64Builder>(col)
                    .unwrap()
                    .append_value(val);
            }
            sb.append(true);
        }
    }
    let array = sb.finish();
    crate::arena::alloc(CantorStructVec { array })
}

// ── Nested vectors (X** at any depth) ────────────────────────────────────────
//
// Kind::Vector(Kind::Vector(K)) — and deeper nestings — are backed by
// `CantorListVec`, an Apache Arrow `Int64Array` of opaque i64 element values.
//
// For a flat X*, elements are scalars (e.g. actual i64 integers or 0/1 bools).
// For X**, each element is an i64 *pointer* to an inner Cantor vector object
// (CantorVecI64, CantorVecBool, CantorListVec, CantorStructVec, …).
// This is the same convention that CantorStructVec uses for its field columns:
// all values are stored as i64, with the semantic meaning known only to the
// codegen from the Kind type system.
//
// The ABI is fully generic — no type suffix, no Arrow type leaking into codegen:
//   cantor_list_vec_builder_new  / push / finish
//   cantor_list_vec_len / get / concat
//
// The six functions work identically for Nat**, Nat***, Bool**, (A*B)**, etc.
//
// NOTE on Arrow's ListArray: Arrow's ListArray models an *array of variable-
// length lists* (each element is itself a list of inlined sub-elements). Using
// it here would require type- and depth-aware builders that inline inner data,
// which would break this generic pointer-erasing ABI. `Int64Array` is the right
// backing here; adopting ListArray properly is a larger rearchitecture of the
// nested-vector ABI.

/// Outer vector for X** at any nesting depth.
/// Elements are i64 values — scalars for X* (handled elsewhere), or opaque
/// pointers to inner Cantor vector objects for X** and deeper.
///
/// `elems` is `pub(crate)` (not `Clone`-derived, unlike the flat vectors
/// above): each element may itself be a pointer to an inner vector object
/// that also lives in the arena, so a plain Arc-bump clone of this array
/// alone would leave those inner objects unreachable from the copy —
/// `deep_copy.rs` walks and re-copies each element explicitly instead.
pub struct CantorListVec {
    pub(crate) elems: Int64Array,
}

pub struct CantorListVecBuilder {
    builder: Int64Builder,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_new() -> i64 {
    crate::arena::alloc(CantorListVecBuilder {
        builder: Int64Builder::new(),
    })
}

/// Append one element (an i64 pointer to an inner vector, or any i64) to the builder.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_push(builder: i64, elem: i64) {
    unsafe { &mut *(builder as *mut CantorListVecBuilder) }
        .builder
        .append_value(elem);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_finish(builder: i64) -> i64 {
    let b = unsafe { &mut *(builder as *mut CantorListVecBuilder) };
    let elems = b.builder.finish();
    crate::arena::alloc(CantorListVec { elems })
}

/// Length of the outer list — valid for any depth.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_len(vec: i64) -> i64 {
    unsafe { &*(vec as *const CantorListVec) }.elems.len() as i64
}

/// Return the i64 element at `idx` (an opaque pointer for nested vectors,
/// or a scalar for flat X* built via this path).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_get(vec: i64, idx: i64) -> i64 {
    unsafe { &*(vec as *const CantorListVec) }
        .elems
        .value(idx as usize)
}

/// Concatenate two CantorListVec values (purely functional, O(n)).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_concat(va: i64, vb: i64) -> i64 {
    let a = unsafe { &*(va as *const CantorListVec) };
    let b = unsafe { &*(vb as *const CantorListVec) };
    let mut builder = Int64Builder::with_capacity(a.elems.len() + b.elems.len());
    for i in 0..a.elems.len() {
        builder.append_value(a.elems.value(i));
    }
    for i in 0..b.elems.len() {
        builder.append_value(b.elems.value(i));
    }
    crate::arena::alloc(CantorListVec {
        elems: builder.finish(),
    })
}

// ── Union vectors ((A | B)* with at least one Tuple arm) ─────────────────────
//
// Kind::Vector(Kind::TaggedUnion(arms)) is backed by a CantorUnionVec wrapping
// an Apache Arrow DenseUnionArray.  Each arm `i` has a StructArray child with
// `leaf_count(arm_i)` Int64Array columns.  Single-leaf arms (scalars) still use
// a 1-column StructArray for uniform access.
//
// ABI contract (codegen responsibilities):
//   1. Call `cantor_union_vec_builder_new(n_arms)` to create a builder.
//   2. For each arm i, call `cantor_union_vec_builder_set_arm(b, i, n_leaves_i)`.
//   3. For each row (element), call `cantor_union_vec_builder_push_leaf(b, arm_i, li, v)`
//      for li = 0 .. n_leaves_i - 1.  The last push auto-commits the row.
//      Extra pushes with li >= n_leaves_i are silently ignored.
//   4. Call `cantor_union_vec_builder_finish(b)` to get the frozen vec pointer.

pub struct CantorUnionVecBuilder {
    n_arms: usize,
    arm_leaf_counts: Vec<usize>,
    arm_col_builders: Vec<Vec<Int64Builder>>,
    type_ids: Vec<i8>,
    offsets: Vec<i32>,
    arm_row_counts: Vec<usize>,
    in_row: bool,
    current_arm: usize,
    leaves_pushed: usize,
}

pub struct CantorUnionVec {
    array: UnionArray,
    arm_leaf_counts: Vec<usize>,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_builder_new(n_arms: i64) -> i64 {
    let n = n_arms as usize;
    crate::arena::alloc(CantorUnionVecBuilder {
        n_arms: n,
        arm_leaf_counts: vec![0; n],
        arm_col_builders: (0..n).map(|_| vec![]).collect(),
        type_ids: Vec::new(),
        offsets: Vec::new(),
        arm_row_counts: vec![0; n],
        in_row: false,
        current_arm: 0,
        leaves_pushed: 0,
    })
}

/// Register arm `arm_idx` as having `n_leaves` leaf columns.
/// Must be called for every arm before any `push_leaf` calls.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_builder_set_arm(builder: i64, arm_idx: i64, n_leaves: i64) {
    let b = unsafe { &mut *(builder as *mut CantorUnionVecBuilder) };
    let ai = arm_idx as usize;
    let nl = n_leaves as usize;
    b.arm_leaf_counts[ai] = nl;
    b.arm_col_builders[ai] = (0..nl).map(|_| Int64Builder::new()).collect();
}

/// Append leaf `leaf_idx` of arm `arm_idx` for the current row.
///
/// When `leaf_idx == 0` a new row begins.  The row is committed automatically
/// when `leaf_idx == arm_leaf_counts[arm_idx] - 1`.  Pushes where
/// `leaf_idx >= arm_leaf_counts[arm_idx]` are silently ignored so that the
/// codegen can always push `max_leaf_count` times per element without branching.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_builder_push_leaf(
    builder: i64,
    arm_idx: i64,
    leaf_idx: i64,
    value: i64,
) {
    let b = unsafe { &mut *(builder as *mut CantorUnionVecBuilder) };
    let ai = arm_idx as usize;
    let li = leaf_idx as usize;
    let n_leaves = b.arm_leaf_counts[ai];

    if li == 0 {
        b.in_row = true;
        b.current_arm = ai;
        b.leaves_pushed = 0;
    }

    if b.in_row && li < n_leaves {
        b.arm_col_builders[ai][li].append_value(value);
        b.leaves_pushed += 1;
        if b.leaves_pushed == n_leaves {
            let offset = b.arm_row_counts[ai] as i32;
            b.type_ids.push(ai as i8);
            b.offsets.push(offset);
            b.arm_row_counts[ai] += 1;
            b.in_row = false;
        }
    }
}

/// Consume the builder, assemble a DenseUnionArray, and return a frozen CantorUnionVec.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_builder_finish(builder: i64) -> i64 {
    let b = unsafe { &mut *(builder as *mut CantorUnionVecBuilder) };
    let arm_leaf_counts = b.arm_leaf_counts.clone();

    let mut children: Vec<ArrayRef> = Vec::with_capacity(b.n_arms);
    let mut union_field_list: Vec<(i8, Arc<Field>)> = Vec::with_capacity(b.n_arms);

    for (ai, col_builders) in b.arm_col_builders.iter_mut().enumerate() {
        let n_leaves = b.arm_leaf_counts[ai];
        let arm_fields: Fields = (0..n_leaves)
            .map(|j| Arc::new(Field::new(format!("l{j}"), DataType::Int64, false)))
            .collect::<Vec<_>>()
            .into();
        let columns: Vec<ArrayRef> = col_builders
            .iter_mut()
            .map(|bld| Arc::new(bld.finish()) as ArrayRef)
            .collect();
        let struct_arr = StructArray::new(arm_fields.clone(), columns, None);
        children.push(Arc::new(struct_arr));
        union_field_list.push((
            ai as i8,
            Arc::new(Field::new(
                format!("arm{ai}"),
                DataType::Struct(arm_fields),
                false,
            )),
        ));
    }

    let union_fields: UnionFields = union_field_list.into_iter().collect();
    let type_ids_buf: ScalarBuffer<i8> = b.type_ids.clone().into();
    let offsets_buf: ScalarBuffer<i32> = b.offsets.clone().into();

    let array = UnionArray::try_new(union_fields, type_ids_buf, Some(offsets_buf), children)
        .expect("cantor_union_vec_builder_finish: UnionArray::try_new failed");

    crate::arena::alloc(CantorUnionVec {
        array,
        arm_leaf_counts,
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_len(vec: i64) -> i64 {
    unsafe { &*(vec as *const CantorUnionVec) }.array.len() as i64
}

/// Return the arm index (type_id) of row `row_idx` as i64.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_get_tag(vec: i64, row_idx: i64) -> i64 {
    let v = unsafe { &*(vec as *const CantorUnionVec) };
    v.array.type_id(row_idx as usize) as i64
}

/// Return leaf `leaf_idx` of row `row_idx`.
///
/// Looks up the arm's StructArray child via the DenseUnionArray offsets buffer,
/// then reads the Int64Array column at `leaf_idx`.
///
/// Returns 0 when `leaf_idx >= arm_leaf_count` — the codegen emits `max_leaves`
/// get_leaf calls for every element regardless of arm width, so narrower arms
/// get padding zeros for the extra slots.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_get_leaf(vec: i64, row_idx: i64, leaf_idx: i64) -> i64 {
    let v = unsafe { &*(vec as *const CantorUnionVec) };
    let row = row_idx as usize;
    let li = leaf_idx as usize;
    let type_id = v.array.type_id(row);
    if li >= v.arm_leaf_counts[type_id as usize] {
        return 0;
    }
    let offset = v.array.value_offset(row);
    v.array
        .child(type_id)
        .as_any()
        .downcast_ref::<StructArray>()
        .expect("union child must be StructArray")
        .column(li)
        .as_any()
        .downcast_ref::<Int64Array>()
        .expect("union child column must be Int64Array")
        .value(offset)
}

/// Concatenate two union vectors of identical arm layout (purely functional, O(n)).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_union_vec_concat(va: i64, vb: i64) -> i64 {
    let a = unsafe { &*(va as *const CantorUnionVec) };
    let b = unsafe { &*(vb as *const CantorUnionVec) };
    assert_eq!(
        a.arm_leaf_counts, b.arm_leaf_counts,
        "cantor_union_vec_concat: arm layout mismatch",
    );

    let n_arms = a.arm_leaf_counts.len() as i64;
    let out = cantor_union_vec_builder_new(n_arms);
    for (ai, &nl) in a.arm_leaf_counts.iter().enumerate() {
        cantor_union_vec_builder_set_arm(out, ai as i64, nl as i64);
    }

    for arr in [&a.array, &b.array] {
        for row in 0..arr.len() {
            let type_id = arr.type_id(row);
            let offset = arr.value_offset(row);
            let ai = type_id as usize;
            let n_leaves = a.arm_leaf_counts[ai];
            let child = arr
                .child(type_id)
                .as_any()
                .downcast_ref::<StructArray>()
                .expect("union child must be StructArray");
            for li in 0..n_leaves {
                let val = child
                    .column(li)
                    .as_any()
                    .downcast_ref::<Int64Array>()
                    .expect("union child column must be Int64Array")
                    .value(offset);
                cantor_union_vec_builder_push_leaf(out, ai as i64, li as i64, val);
            }
        }
    }

    cantor_union_vec_builder_finish(out)
}

// ── Checked arithmetic (int-soundness-plan phase 1) ────────────────────────────

/// Print an overflow message and exit nonzero. Called from a checked-arithmetic
/// abort block; codegen emits `unreachable` immediately after the call, so this
/// never needs to return control to the caller.
///
/// `msg_ptr` points at a null-terminated string baked into the module as a
/// global constant at compile time.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_overflow_abort(msg_ptr: i64) {
    let msg = unsafe { std::ffi::CStr::from_ptr(msg_ptr as *const i8) };
    eprintln!("{}", msg.to_string_lossy());
    std::process::exit(1);
}

// ── Overload runtime dispatch (int-soundness-plan phase 2) ────────────────────

/// Print a message and exit nonzero. Called from an overload runtime-dispatch
/// chain's final else-arm — reached only if no candidate's domain matched,
/// which the solver proved can't happen; codegen emits `unreachable`
/// immediately after the call, so this never needs to return control.
///
/// `msg_ptr` points at a null-terminated string baked into the module as a
/// global constant at compile time.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_dispatch_unreachable(msg_ptr: i64) {
    let msg = unsafe { std::ffi::CStr::from_ptr(msg_ptr as *const i8) };
    eprintln!("{}", msg.to_string_lossy());
    std::process::exit(1);
}

pub mod arena;
mod bigint;
pub mod deep_copy;
pub mod event_loop;
pub use bigint::*;
