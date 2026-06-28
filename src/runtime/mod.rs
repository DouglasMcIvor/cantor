//! Cantor runtime library — called from JIT-compiled code via extern "C" ABI.
//!
//! All pointer arguments cross the ABI boundary as i64 (pointer-as-i64),
//! matching the compiler's uniform i64 calling convention.
//!
//! Memory: sets and vectors are heap-allocated with Box::into_raw and never freed.
//! TODO: replace with an arena scoped to the event-handler dispatch boundary.

use std::sync::Arc;

use arrow_array::{
    Array, BooleanArray, Int64Array, StructArray,
    builder::{ArrayBuilder, BooleanBuilder, Int64Builder, StructBuilder},
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
    builder: StructBuilder,
}

fn make_struct_builder(n: usize) -> StructBuilder {
    let fields: Fields = (0..n)
        .map(|i| Arc::new(Field::new(format!("f{i}"), DataType::Int64, false)))
        .collect::<Vec<_>>()
        .into();
    let field_builders: Vec<Box<dyn ArrayBuilder>> =
        (0..n).map(|_| Box::new(Int64Builder::new()) as Box<dyn ArrayBuilder>).collect();
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
    b.builder.field_builder::<Int64Builder>(idx).unwrap().append_value(value);
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
    assert_eq!(n, vb.array.num_columns(), "cantor_struct_vec_concat: field count mismatch");
    let mut sb = make_struct_builder(n);
    for sv in [&va.array, &vb.array] {
        for row in 0..sv.len() {
            for col in 0..n {
                let val = sv.column(col)
                    .as_any()
                    .downcast_ref::<Int64Array>()
                    .expect("struct col must be Int64Array")
                    .value(row);
                sb.field_builder::<Int64Builder>(col).unwrap().append_value(val);
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
    Box::into_raw(Box::new(CantorListVecBuilder { builder: Int64Builder::new() })) as i64
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
    unsafe { &*(vec as *const CantorListVec) }.elems.value(idx as usize)
}

/// Concatenate two CantorListVec values (purely functional, O(n)).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_list_vec_concat(va: i64, vb: i64) -> i64 {
    let a = unsafe { &*(va as *const CantorListVec) };
    let b = unsafe { &*(vb as *const CantorListVec) };
    let mut builder = Int64Builder::with_capacity(a.elems.len() + b.elems.len());
    for i in 0..a.elems.len() { builder.append_value(a.elems.value(i)); }
    for i in 0..b.elems.len() { builder.append_value(b.elems.value(i)); }
    Box::into_raw(Box::new(CantorListVec { elems: builder.finish() })) as i64
}
