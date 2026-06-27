//! Cantor runtime library — called from JIT-compiled code via extern "C" ABI.
//!
//! All pointer arguments cross the ABI boundary as i64 (pointer-as-i64),
//! matching the compiler's uniform i64 calling convention.
//!
//! Memory: sets and vectors are heap-allocated with Box::into_raw and never freed.
//! TODO: replace with an arena scoped to the event-handler dispatch boundary.

use arrow_array::{
    BooleanArray, Int64Array,
    builder::{BooleanBuilder, Int64Builder},
};

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
