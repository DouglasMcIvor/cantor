//! Cantor runtime library — called from JIT-compiled code via extern "C" ABI.
//!
//! All pointer arguments cross the ABI boundary as i64 (pointer-as-i64),
//! matching the compiler's uniform i64 calling convention.
//!
//! Memory: sets and vectors are heap-allocated with Box::into_raw and never freed.
//! TODO: replace with an arena scoped to the event-handler dispatch boundary.

use std::sync::Arc;

use arrow_array::{
    Array, ArrayRef, BooleanArray, Int64Array, ListArray, StructArray,
    builder::{BooleanBuilder, Int64Builder, ListBuilder},
};
use arrow_schema::{DataType, Field, Fields};

// ── Int set ───────────────────────────────────────────────────────────────────

/// A finite set of i64 values, stored sorted for O(log n) membership testing.
pub struct CantorIntSet {
    elements: Vec<i64>,
}

impl Default for CantorIntSet {
    fn default() -> Self {
        Self { elements: Vec::new() }
    }
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
pub struct CantorBoolSet {
    elements: Vec<bool>,
}

impl Default for CantorBoolSet {
    fn default() -> Self {
        Self { elements: Vec::new() }
    }
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
    unsafe { &*(vec as *const CantorVecI64) }.array.value(idx as usize)
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
    Box::into_raw(Box::new(CantorVecI64 { array: builder.finish() })) as i64
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
    unsafe { &*(vec as *const CantorVecBool) }.array.value(idx as usize) as i64
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
    Box::into_raw(Box::new(CantorVecBool { array: builder.finish() })) as i64
}

// ── Vector concatenation ──────────────────────────────────────────────────────

/// Concatenate two Int* vectors into a new one.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_concat_i64(a: i64, b: i64) -> i64 {
    let va = unsafe { &*(a as *const CantorVecI64) };
    let vb = unsafe { &*(b as *const CantorVecI64) };
    let mut builder = Int64Builder::with_capacity(va.array.len() + vb.array.len());
    for i in 0..va.array.len() { builder.append_value(va.array.value(i)); }
    for i in 0..vb.array.len() { builder.append_value(vb.array.value(i)); }
    Box::into_raw(Box::new(CantorVecI64 { array: builder.finish() })) as i64
}

/// Concatenate two Bool* vectors into a new one.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_vec_concat_bool(a: i64, b: i64) -> i64 {
    let va = unsafe { &*(a as *const CantorVecBool) };
    let vb = unsafe { &*(b as *const CantorVecBool) };
    let mut builder = BooleanBuilder::with_capacity(va.array.len() + vb.array.len());
    for i in 0..va.array.len() { builder.append_value(va.array.value(i)); }
    for i in 0..vb.array.len() { builder.append_value(vb.array.value(i)); }
    Box::into_raw(Box::new(CantorVecBool { array: builder.finish() })) as i64
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
    builders: Vec<Int64Builder>,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_builder_new(n_fields: i64) -> i64 {
    let n = n_fields as usize;
    Box::into_raw(Box::new(CantorStructVecBuilder {
        n_fields: n,
        builders: (0..n).map(|_| Int64Builder::new()).collect(),
    })) as i64
}

/// Append `value` to column `field_idx` of the current row.
/// Bool values are already widened to 0/1 i64 by the codegen.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_builder_push_field(builder: i64, field_idx: i64, value: i64) {
    let b = unsafe { &mut *(builder as *mut CantorStructVecBuilder) };
    b.builders[field_idx as usize].append_value(value);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_struct_vec_builder_finish(builder: i64) -> i64 {
    let mut b = unsafe { Box::from_raw(builder as *mut CantorStructVecBuilder) };
    let n = b.n_fields;
    let columns: Vec<Int64Array> = b.builders.iter_mut().map(|bld| bld.finish()).collect();
    let fields: Fields = (0..n)
        .map(|i| Arc::new(Field::new(format!("f{i}"), DataType::Int64, false)))
        .collect::<Vec<_>>()
        .into();
    let arrays: Vec<ArrayRef> = columns.into_iter()
        .map(|c| Arc::new(c) as ArrayRef)
        .collect();
    let array = StructArray::try_new(fields, arrays, None)
        .expect("CantorStructVec: StructArray construction failed");
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
    assert_eq!(n, vb.array.num_columns(), "cantor_struct_vec_concat: field count mismatch");
    let mut builders: Vec<Int64Builder> = (0..n).map(|_| Int64Builder::new()).collect();
    for sv in [&va.array, &vb.array] {
        for (col_idx, col) in sv.columns().iter().enumerate() {
            let arr = col.as_any().downcast_ref::<Int64Array>()
                .expect("struct col must be Int64Array");
            for i in 0..arr.len() { builders[col_idx].append_value(arr.value(i)); }
        }
    }
    let fields: Fields = (0..n)
        .map(|i| Arc::new(Field::new(format!("f{i}"), DataType::Int64, false)))
        .collect::<Vec<_>>()
        .into();
    let arrays: Vec<ArrayRef> = builders.iter_mut()
        .map(|bld| Arc::new(bld.finish()) as ArrayRef)
        .collect();
    let array = StructArray::try_new(fields, arrays, None)
        .expect("cantor_struct_vec_concat: StructArray construction failed");
    Box::into_raw(Box::new(CantorStructVec { array })) as i64
}

// ── Nested vectors (X**) ──────────────────────────────────────────────────────
//
// Kind::Vector(Kind::Vector(K)) is backed by Apache Arrow ListArray.
//
// The unified `CantorListVec` holds a ListArray whose child ArrayRef varies
// by depth:
//   Nat** (K=Int):  child is Int64Array
//   Bool** (K=Bool): child is BooleanArray
//   Nat*** (K=Vector(Int)): child is ListArray (itself a Nat** ListArray)
//
// Builders are separate concrete types per child kind (typed Arrow builders).
// The result is always CantorListVec regardless of depth.
//
// Arrow ListArray layout: offsets buffer + contiguous child array.
// Element i spans child_array[offsets[i]..offsets[i+1]] — zero-copy slice
// for scalar children; copied into a new CantorListVec for list children.

/// Unified outer vector for X** at any nesting depth.
pub struct CantorListVec {
    array: ListArray,
}

// ── Nat** — List<Int64> ───────────────────────────────────────────────────────

pub struct CantorListVecBuilderI64 {
    builder: ListBuilder<Int64Builder>,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_new_i64() -> i64 {
    Box::into_raw(Box::new(CantorListVecBuilderI64 {
        builder: ListBuilder::new(Int64Builder::new()),
    })) as i64
}

/// Append the contents of `inner_vec` (a `CantorVecI64` pointer) as the next element.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_push_i64(builder: i64, inner_vec: i64) {
    let b = unsafe { &mut *(builder as *mut CantorListVecBuilderI64) };
    let inner = unsafe { &*(inner_vec as *const CantorVecI64) };
    for i in 0..inner.array.len() {
        b.builder.values().append_value(inner.array.value(i));
    }
    b.builder.append(true);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_finish_i64(builder: i64) -> i64 {
    let mut b = unsafe { Box::from_raw(builder as *mut CantorListVecBuilderI64) };
    let array = b.builder.finish();
    Box::into_raw(Box::new(CantorListVec { array })) as i64
}

// ── Bool** — List<Boolean> ────────────────────────────────────────────────────

pub struct CantorListVecBuilderBool {
    builder: ListBuilder<BooleanBuilder>,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_new_bool() -> i64 {
    Box::into_raw(Box::new(CantorListVecBuilderBool {
        builder: ListBuilder::new(BooleanBuilder::new()),
    })) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_push_bool(builder: i64, inner_vec: i64) {
    let b = unsafe { &mut *(builder as *mut CantorListVecBuilderBool) };
    let inner = unsafe { &*(inner_vec as *const CantorVecBool) };
    for i in 0..inner.array.len() {
        b.builder.values().append_value(inner.array.value(i));
    }
    b.builder.append(true);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_finish_bool(builder: i64) -> i64 {
    let mut b = unsafe { Box::from_raw(builder as *mut CantorListVecBuilderBool) };
    let array = b.builder.finish();
    Box::into_raw(Box::new(CantorListVec { array })) as i64
}

// ── Nat*** — List<List<Int64>> ────────────────────────────────────────────────

pub struct CantorListVecBuilderListI64 {
    builder: ListBuilder<ListBuilder<Int64Builder>>,
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_new_list_i64() -> i64 {
    Box::into_raw(Box::new(CantorListVecBuilderListI64 {
        builder: ListBuilder::new(ListBuilder::new(Int64Builder::new())),
    })) as i64
}

/// Append the contents of `inner_list` (a `CantorListVec` pointer over Int64) as the next element.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_push_list_i64(outer_builder: i64, inner_list: i64) {
    let b = unsafe { &mut *(outer_builder as *mut CantorListVecBuilderListI64) };
    let inner = unsafe { &*(inner_list as *const CantorListVec) };
    let inner_la = &inner.array;
    let inner_vals = inner_la
        .values()
        .as_any()
        .downcast_ref::<Int64Array>()
        .expect("push_list_i64: inner CantorListVec must have Int64Array child");
    for i in 0..inner_la.len() {
        let start = inner_la.value_offsets()[i] as usize;
        let end   = inner_la.value_offsets()[i + 1] as usize;
        for j in start..end {
            b.builder.values().values().append_value(inner_vals.value(j));
        }
        b.builder.values().append(true);
    }
    b.builder.append(true);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_builder_finish_list_i64(builder: i64) -> i64 {
    let mut b = unsafe { Box::from_raw(builder as *mut CantorListVecBuilderListI64) };
    let array = b.builder.finish();
    Box::into_raw(Box::new(CantorListVec { array })) as i64
}

// ── Shared read operations on CantorListVec ───────────────────────────────────

/// Length of the outer vector — same for all child kinds.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_len(vec: i64) -> i64 {
    unsafe { &*(vec as *const CantorListVec) }.array.len() as i64
}

/// Return element `idx` as a new `CantorVecI64` pointer (for Nat**).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_get_i64(vec: i64, idx: i64) -> i64 {
    let list = unsafe { &*(vec as *const CantorListVec) };
    let slice = list.array.value(idx as usize);
    let inner = slice
        .as_any()
        .downcast_ref::<Int64Array>()
        .expect("cantor_list_vec_get_i64: child must be Int64Array")
        .clone();
    Box::into_raw(Box::new(CantorVecI64 { array: inner })) as i64
}

/// Return element `idx` as a new `CantorVecBool` pointer (for Bool**).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_get_bool(vec: i64, idx: i64) -> i64 {
    let list = unsafe { &*(vec as *const CantorListVec) };
    let slice = list.array.value(idx as usize);
    let inner = slice
        .as_any()
        .downcast_ref::<BooleanArray>()
        .expect("cantor_list_vec_get_bool: child must be BooleanArray")
        .clone();
    Box::into_raw(Box::new(CantorVecBool { array: inner })) as i64
}

/// Return element `idx` as a new `CantorListVec` pointer (for Nat***).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_get_list_i64(vec: i64, idx: i64) -> i64 {
    let list = unsafe { &*(vec as *const CantorListVec) };
    let slice = list.array.value(idx as usize);
    let inner = slice
        .as_any()
        .downcast_ref::<ListArray>()
        .expect("cantor_list_vec_get_list_i64: child must be ListArray")
        .clone();
    Box::into_raw(Box::new(CantorListVec { array: inner })) as i64
}

// ── Concatenation for CantorListVec ──────────────────────────────────────────

/// Concatenate two Nat** vectors (child = Int64Array).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_concat_i64(va: i64, vb: i64) -> i64 {
    let a = unsafe { &*(va as *const CantorListVec) };
    let b = unsafe { &*(vb as *const CantorListVec) };
    let mut builder = ListBuilder::new(Int64Builder::new());
    for list in [&a.array, &b.array] {
        for i in 0..list.len() {
            let slice = list.value(i);
            let inner = slice.as_any().downcast_ref::<Int64Array>().unwrap();
            for j in 0..inner.len() { builder.values().append_value(inner.value(j)); }
            builder.append(true);
        }
    }
    Box::into_raw(Box::new(CantorListVec { array: builder.finish() })) as i64
}

/// Concatenate two Bool** vectors (child = BooleanArray).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_concat_bool(va: i64, vb: i64) -> i64 {
    let a = unsafe { &*(va as *const CantorListVec) };
    let b = unsafe { &*(vb as *const CantorListVec) };
    let mut builder = ListBuilder::new(BooleanBuilder::new());
    for list in [&a.array, &b.array] {
        for i in 0..list.len() {
            let slice = list.value(i);
            let inner = slice.as_any().downcast_ref::<BooleanArray>().unwrap();
            for j in 0..inner.len() { builder.values().append_value(inner.value(j)); }
            builder.append(true);
        }
    }
    Box::into_raw(Box::new(CantorListVec { array: builder.finish() })) as i64
}

/// Concatenate two Nat*** vectors (child = ListArray<Int64>).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_concat_list_i64(va: i64, vb: i64) -> i64 {
    let a = unsafe { &*(va as *const CantorListVec) };
    let b = unsafe { &*(vb as *const CantorListVec) };
    let mut builder = ListBuilder::new(ListBuilder::new(Int64Builder::new()));
    for list in [&a.array, &b.array] {
        for i in 0..list.len() {
            let outer_slice = list.value(i);
            let inner_la = outer_slice.as_any().downcast_ref::<ListArray>()
                .expect("cantor_list_vec_concat_list_i64: inner must be ListArray");
            let inner_vals = inner_la.values().as_any().downcast_ref::<Int64Array>()
                .expect("cantor_list_vec_concat_list_i64: inner values must be Int64Array");
            for j in 0..inner_la.len() {
                let start = inner_la.value_offsets()[j] as usize;
                let end   = inner_la.value_offsets()[j + 1] as usize;
                for k in start..end {
                    builder.values().values().append_value(inner_vals.value(k));
                }
                builder.values().append(true);
            }
            builder.append(true);
        }
    }
    Box::into_raw(Box::new(CantorListVec { array: builder.finish() })) as i64
}
