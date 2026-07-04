//! Cantor runtime library — called from JIT-compiled code via extern "C" ABI.
//!
//! All pointer arguments cross the ABI boundary as i64 (pointer-as-i64),
//! matching the compiler's uniform i64 calling convention.
//!
//! Memory: sets and vectors are heap-allocated with Box::into_raw and never freed.
//! TODO: replace with an arena scoped to the event-handler dispatch boundary.

use std::sync::Arc;

use arrow_array::{
    Array, ArrayRef, BooleanArray, Int64Array, StructArray, UnionArray,
    builder::{ArrayBuilder, BooleanBuilder, Int64Builder, StructBuilder},
};
use arrow_buffer::ScalarBuffer;
use arrow_schema::{DataType, Field, Fields, UnionFields};

// ── Int set ───────────────────────────────────────────────────────────────────

/// A finite set of i64 values, stored sorted for O(log n) membership testing.
#[derive(Default)]
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
    Box::into_raw(Box::new(CantorIntSet::default())) as i64
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
#[derive(Default)]
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
    Box::into_raw(Box::new(CantorBoolSet::default())) as i64
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

pub struct CantorVecI64 {
    array: Int64Array,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_new_i64() -> i64 {
    Box::into_raw(Box::new(CantorVecBuilderI64 {
        builder: Int64Builder::new(),
    })) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_push_i64(builder: i64, val: i64) {
    unsafe { &mut *(builder as *mut CantorVecBuilderI64) }
        .builder
        .append_value(val);
}

/// Consume the builder and return a pointer to a frozen `CantorVecI64`.
/// The builder is freed; the returned vec is heap-allocated (Box::into_raw).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_finish_i64(builder: i64) -> i64 {
    let mut b = unsafe { Box::from_raw(builder as *mut CantorVecBuilderI64) };
    let array = b.builder.finish();
    Box::into_raw(Box::new(CantorVecI64 { array })) as i64
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
    Box::into_raw(Box::new(CantorVecI64 {
        array: builder.finish(),
    })) as i64
}

// ── Bool vector (Kind::Vector(Kind::Bool)) ────────────────────────────────────
//
// Same design as the Int vector but backed by `BooleanArray`.
// ABI passes booleans as i64 (0 = false, non-zero = true).

pub struct CantorVecBuilderBool {
    builder: BooleanBuilder,
}

pub struct CantorVecBool {
    array: BooleanArray,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_new_bool() -> i64 {
    Box::into_raw(Box::new(CantorVecBuilderBool {
        builder: BooleanBuilder::new(),
    })) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_push_bool(builder: i64, val: i64) {
    unsafe { &mut *(builder as *mut CantorVecBuilderBool) }
        .builder
        .append_value(val != 0);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_builder_finish_bool(builder: i64) -> i64 {
    let mut b = unsafe { Box::from_raw(builder as *mut CantorVecBuilderBool) };
    let array = b.builder.finish();
    Box::into_raw(Box::new(CantorVecBool { array })) as i64
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
    Box::into_raw(Box::new(CantorVecBool {
        array: builder.finish(),
    })) as i64
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
    Box::into_raw(Box::new(CantorVecI64 {
        array: builder.finish(),
    })) as i64
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
    Box::into_raw(Box::new(CantorVecBool {
        array: builder.finish(),
    })) as i64
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
    Box::into_raw(Box::new(CantorStructVecBuilder {
        n_fields: n,
        builder: make_struct_builder(n),
    })) as i64
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
    let mut b = unsafe { Box::from_raw(builder as *mut CantorStructVecBuilder) };
    let array = b.builder.finish();
    Box::into_raw(Box::new(CantorStructVec { array })) as i64
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
    Box::into_raw(Box::new(CantorStructVec { array })) as i64
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
pub struct CantorListVec {
    elems: Int64Array,
}

pub struct CantorListVecBuilder {
    builder: Int64Builder,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_new() -> i64 {
    Box::into_raw(Box::new(CantorListVecBuilder {
        builder: Int64Builder::new(),
    })) as i64
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
    let mut b = unsafe { Box::from_raw(builder as *mut CantorListVecBuilder) };
    let elems = b.builder.finish();
    Box::into_raw(Box::new(CantorListVec { elems })) as i64
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
    Box::into_raw(Box::new(CantorListVec {
        elems: builder.finish(),
    })) as i64
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
    Box::into_raw(Box::new(CantorUnionVecBuilder {
        n_arms: n,
        arm_leaf_counts: vec![0; n],
        arm_col_builders: (0..n).map(|_| vec![]).collect(),
        type_ids: Vec::new(),
        offsets: Vec::new(),
        arm_row_counts: vec![0; n],
        in_row: false,
        current_arm: 0,
        leaves_pushed: 0,
    })) as i64
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
    let mut b = unsafe { Box::from_raw(builder as *mut CantorUnionVecBuilder) };
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
    let type_ids_buf: ScalarBuffer<i8> = b.type_ids.into();
    let offsets_buf: ScalarBuffer<i32> = b.offsets.into();

    let array = UnionArray::try_new(union_fields, type_ids_buf, Some(offsets_buf), children)
        .expect("cantor_union_vec_builder_finish: UnionArray::try_new failed");

    Box::into_raw(Box::new(CantorUnionVec {
        array,
        arm_leaf_counts,
    })) as i64
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

// ── BigInt (int-soundness-plan phase 3, step 1: runtime only) ─────────────────
//
// Representation (design-decisions.md §13, int-soundness-plan.md "Phase 3"):
// unbounded `Int`/`Nat` positions are a one-word tagged value, not a plain
// i64 or an `{i1, i64}` struct:
//   - low bit 0 → small integer, value = `word >> 1` (arithmetic shift).
//     Range: [-2^62, 2^62 - 1] — one bit narrower than `Int64` itself, since
//     the tag consumes a bit. A value that fits in i64 but not in this
//     narrower "small" range (the band near Int64's own extremes) boxes.
//   - low bit 1 → pointer to a heap-allocated `CantorBigInt`.
//
// `CantorBigInt` is `Box::into_raw` and never freed, exactly like every other
// heap object in this file (see the module doc comment) — no refcounting/GC
// is introduced for this feature specifically.
//
// Every `cantor_bigint_*` entry point below takes/returns tagged words, never
// raw `BigInt`s or un-tagged i64s, so codegen never has to case-split between
// "both small", "both big", "mixed" itself — each function decides that
// internally. The "both small" case stays on plain i64/i128 arithmetic
// (cheap); arbitrary-precision (`num_bigint`) arithmetic only runs once an
// operand is already boxed.

use num_bigint::BigInt;

/// One bit narrower than `Int64`'s own range — see the module comment above.
/// `pub` so codegen can constant-fold a small literal's tagged encoding
/// directly at compile time instead of always emitting a runtime call.
pub const TAG_SMALL_MIN: i64 = -(1i64 << 62);
pub const TAG_SMALL_MAX: i64 = (1i64 << 62) - 1;

#[repr(align(8))]
pub struct CantorBigInt(BigInt);

/// Encode `n` as a tagged small-int word, or `None` if `n` is outside the
/// tagged scheme's narrower small-int range (caller must box instead).
fn encode_small(n: i64) -> Option<i64> {
    if (TAG_SMALL_MIN..=TAG_SMALL_MAX).contains(&n) {
        Some(n << 1)
    } else {
        None
    }
}

/// Heap-allocate `v` and tag the pointer. Never freed (see module doc comment).
fn box_bigint(v: BigInt) -> i64 {
    let ptr = Box::into_raw(Box::new(CantorBigInt(v))) as i64;
    ptr | 1
}

/// Encode `v`, choosing the small-int word when it fits, boxing otherwise.
fn encode_bigint(v: BigInt) -> i64 {
    if let Ok(small) = i64::try_from(&v)
        && let Some(word) = encode_small(small)
    {
        return word;
    }
    box_bigint(v)
}

/// Materialize a tagged word as an owned `BigInt` — cheap for small words,
/// clones the heap value for boxed ones. Used once either operand is already
/// boxed, i.e. the arbitrary-precision path; the small/small fast path below
/// never calls this.
fn as_bigint(word: i64) -> BigInt {
    if word & 1 == 0 {
        BigInt::from(word >> 1)
    } else {
        let ptr = (word & !1) as *const CantorBigInt;
        unsafe { (*ptr).0.clone() }
    }
}

/// If both `a` and `b` are small words, returns their decoded (unshifted)
/// values. Each is within `[TAG_SMALL_MIN, TAG_SMALL_MAX]`.
fn both_small(a: i64, b: i64) -> Option<(i64, i64)> {
    if a & 1 == 0 && b & 1 == 0 {
        Some((a >> 1, b >> 1))
    } else {
        None
    }
}

/// Encode a plain i64 (e.g. a raw `Int64`-Kind value, or a literal) as a
/// tagged `Int` word.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_from_i64(n: i64) -> i64 {
    match encode_small(n) {
        Some(word) => word,
        None => box_bigint(BigInt::from(n)),
    }
}

/// Decode a tagged `Int` word into a plain i64 — the inverse of
/// `cantor_bigint_from_i64`. Used at a call boundary where an already-
/// tagged argument is passed to a statically-resolved raw-`Int64`
/// parameter (int-soundness-plan phase 3 step 4b): the solver has already
/// proved the value lies in `Int64` before codegen ever emits this call,
/// so the boxed branch is expected to be rare in practice but must still
/// decode correctly when it does happen (e.g. a value in the tagged
/// scheme's own narrow-small-range wrinkle band, see `runtime/mod.rs`'s
/// module doc comment).
///
/// Aborts (does not panic — a Rust panic can't safely unwind across the
/// `extern "C"` boundary into JIT-compiled code, see `cantor_overflow_abort`
/// for the same reasoning) if the boxed value doesn't actually fit in i64
/// despite that — a real compiler bug (a wrongly-resolved static proof),
/// never a legitimate runtime outcome, so this fails loudly rather than
/// silently truncating.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_to_i64(word: i64) -> i64 {
    if word & 1 == 0 {
        word >> 1
    } else {
        let ptr = (word & !1) as *const CantorBigInt;
        match i64::try_from(unsafe { &(*ptr).0 }) {
            Ok(n) => n,
            Err(_) => {
                eprintln!(
                    "cantor_bigint_to_i64: boxed value doesn't fit in i64 despite a proved \
                     Int64 boundary — compiler invariant violated"
                );
                std::process::exit(1);
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_add(a: i64, b: i64) -> i64 {
    if let Some((x, y)) = both_small(a, b) {
        // x, y ∈ [-2^62, 2^62 - 1], so x + y always fits in a plain i64
        // (no overflow possible) — it just might not fit the narrower
        // small-word range, in which case it boxes.
        return encode_small(x + y).unwrap_or_else(|| box_bigint(BigInt::from(x + y)));
    }
    encode_bigint(as_bigint(a) + as_bigint(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_sub(a: i64, b: i64) -> i64 {
    if let Some((x, y)) = both_small(a, b) {
        // Same reasoning as `add`: x - y always fits in a plain i64.
        return encode_small(x - y).unwrap_or_else(|| box_bigint(BigInt::from(x - y)));
    }
    encode_bigint(as_bigint(a) - as_bigint(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_mul(a: i64, b: i64) -> i64 {
    if let Some((x, y)) = both_small(a, b) {
        // x, y are each 63-bit signed at most, so the product always fits in
        // i128 (up to 126 bits) even though it can exceed i64.
        let product = (x as i128) * (y as i128);
        if let Ok(n) = i64::try_from(product)
            && let Some(word) = encode_small(n)
        {
            return word;
        }
        return box_bigint(BigInt::from(product));
    }
    encode_bigint(as_bigint(a) * as_bigint(b))
}

/// Divisor-nonzero is a hard proof obligation on `/` established before
/// codegen ever emits this call (design-decisions.md "Arithmetic widening") —
/// this function never defends against a zero divisor.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_div(a: i64, b: i64) -> i64 {
    if let Some((x, y)) = both_small(a, b) {
        // Truncates toward zero, matching Cantor's `/` semantics. Dividing
        // never increases magnitude, so the quotient is always representable
        // as a small word (|x / y| <= |x| <= TAG_SMALL_MAX).
        let q = x / y;
        return encode_small(q).expect("quotient of two small values is always small");
    }
    encode_bigint(as_bigint(a) / as_bigint(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_neg(a: i64) -> i64 {
    if a & 1 == 0 {
        let n = a >> 1;
        // n ∈ [-2^62, 2^62 - 1], so -n ∈ [-(2^62 - 1), 2^62] — always a
        // plain i64, but -n = 2^62 overflows the small-word range by one.
        return encode_small(-n).unwrap_or_else(|| box_bigint(BigInt::from(-n)));
    }
    encode_bigint(-as_bigint(a))
}

/// Three-way comparison: -1 (`a < b`), 0 (`a == b`), 1 (`a > b`).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_cmp(a: i64, b: i64) -> i64 {
    use std::cmp::Ordering;
    let ord = if let Some((x, y)) = both_small(a, b) {
        x.cmp(&y)
    } else {
        as_bigint(a).cmp(&as_bigint(b))
    };
    match ord {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

/// Renders `a` in base 10 as a heap-allocated, null-terminated C string —
/// never freed, matching every other allocation in this file. Returns a
/// pointer-as-i64, readable via `CStr::from_ptr`.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_to_string(a: i64) -> i64 {
    let s = if a & 1 == 0 {
        (a >> 1).to_string()
    } else {
        as_bigint(a).to_string()
    };
    let c_string = std::ffi::CString::new(s).expect("BigInt decimal string has no interior NUL");
    c_string.into_raw() as i64
}
