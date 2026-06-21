//! Cantor runtime library — called from JIT-compiled code via extern "C" ABI.
//!
//! All pointer arguments cross the ABI boundary as i64 (pointer-as-i64),
//! matching the compiler's uniform i64 calling convention.
//!
//! Memory: sets are heap-allocated with Box::into_raw and never freed.
//! TODO: replace with an arena scoped to the event-handler dispatch boundary.

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
