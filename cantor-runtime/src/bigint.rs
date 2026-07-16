//! BigInt (int-soundness-plan phase 3, step 1: runtime only) — pure refactor
//! split out of `mod.rs` to keep that file under the repo's line-count
//! guideline (see CLAUDE.md), no behaviour change.
//!
//! Representation (design-decisions.md §13, int-soundness-plan.md "Phase 3"):
//! unbounded `Int`/`Nat` positions are a one-word tagged value, not a plain
//! i64 or an `{i1, i64}` struct:
//!   - low bit 0 → small integer, value = `word >> 1` (arithmetic shift).
//!     Range: [-2^62, 2^62 - 1] — one bit narrower than `Int64` itself, since
//!     the tag consumes a bit. A value that fits in i64 but not in this
//!     narrower "small" range (the band near Int64's own extremes) boxes.
//!   - low bit 1 → pointer to a heap-allocated `CantorBigInt`.
//!
//! `CantorBigInt` is allocated through the `arena` module, exactly like every
//! other heap object in this crate (see `lib.rs`'s module doc comment) — no
//! refcounting/GC is introduced for this feature specifically.
//!
//! Every `cantor_bigint_*` entry point below takes/returns tagged words, never
//! raw `BigInt`s or un-tagged i64s, so codegen never has to case-split between
//! "both small", "both big", "mixed" itself — each function decides that
//! internally. The "both small" case stays on plain i64/i128 arithmetic
//! (cheap); arbitrary-precision (`num_bigint`) arithmetic only runs once an
//! operand is already boxed.

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

/// Arena-allocate `v` and tag the pointer (see `arena.rs` — allocation is
/// registered for a deferred drop, not leaked, though nothing resets the
/// arena yet).
fn box_bigint(v: BigInt) -> i64 {
    crate::arena::alloc(CantorBigInt(v)) | 1
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

/// Same decode as [`cantor_bigint_to_i64`], but for the `Vector(Int)`/
/// `Set(Int)` storage boundary (int-soundness-plan.md's "deliberately stayed
/// raw" container note) rather than a solver-proved call boundary — hitting
/// the failure case here is a legitimate, expected language limitation (a
/// genuinely-unbounded `Int` value pushed into a container that is Int64-only
/// by design), never a compiler bug, so it gets its own message rather than
/// `cantor_bigint_to_i64`'s "compiler invariant violated" wording.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_to_i64_container(word: i64) -> i64 {
    if word & 1 == 0 {
        word >> 1
    } else {
        let ptr = (word & !1) as *const CantorBigInt;
        match i64::try_from(unsafe { &(*ptr).0 }) {
            Ok(n) => n,
            Err(_) => {
                eprintln!(
                    "cantor: a Vector(Int)/Set(Int) element is outside the Int64 range — \
                     containers of Int are Int64-only by design (see \
                     docs/int-soundness-plan.md), not arbitrary-precision"
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

/// Magnitude-aware ordering of two tagged words — the shared logic behind
/// `cantor_bigint_cmp` and `CantorTaggedIntSet`'s dedup/lookup ordering.
/// Cheap for the common all-small case (`both_small`'s shift-and-compare,
/// no allocation); falls back to a real `BigInt` comparison — which decodes
/// through a shared boxed value correctly regardless of *which* heap
/// allocation holds it — only when at least one side is boxed.
fn tagged_cmp(a: i64, b: i64) -> std::cmp::Ordering {
    if let Some((x, y)) = both_small(a, b) {
        x.cmp(&y)
    } else {
        as_bigint(a).cmp(&as_bigint(b))
    }
}

/// Three-way comparison: -1 (`a < b`), 0 (`a == b`), 1 (`a > b`).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_bigint_cmp(a: i64, b: i64) -> i64 {
    use std::cmp::Ordering;
    match tagged_cmp(a, b) {
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

/// Renders `a` in base 10 as a `Char*` (`Vector(Char)`) value — the builtin
/// `show`'s `Int`/`Int64`/`Signed32`/`Unsigned32` case (`codegen::show`,
/// backing string interpolation, `parser::expr`'s `desugar_interp_parts`).
/// Same decimal formatting as `cantor_bigint_to_string`, just packaged as
/// the runtime's ordinary `Char*` Arrow-vector representation (via
/// `event_loop::encode_char_star`, the same builder idiom every other
/// `Char*`/string value in the compiler is built through) instead of a
/// `CString`, so codegen can treat a `show(int)` result identically to any
/// other `Char*` (e.g. feed it straight into `cantor_vec_concat_i64`).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_show_bigint(a: i64) -> i64 {
    let s = if a & 1 == 0 {
        (a >> 1).to_string()
    } else {
        as_bigint(a).to_string()
    };
    crate::event_loop::encode_char_star(&s)
}

// ── Tagged Int set (`Set(Int)` with a possibly-boxed element) ──────────────
//
// `CantorIntSet` (mod.rs) dedups/orders by raw i64 value — correct only when
// every element is a plain untagged word. That breaks the moment a tagged
// `Kind::Int` element can be boxed: two different heap allocations holding
// the same integer are not `==` as raw pointers, and a boxed pointer's
// numeric value bears no relationship to the value it encodes, so both
// dedup and ordering would be nonsense. `CantorTaggedIntSet` instead orders
// by `tagged_cmp` (the same small/boxed logic `cantor_bigint_cmp` uses) —
// cheap for the common all-small case, correct once a boxed value enters
// the set: two boxed allocations of equal value collapse to one entry
// (`insert`'s `Ok(_)` arm keeps the existing entry and drops the redundant
// allocation, consistent with this file's "never freed" memory model).
//
// Only ever call these on genuinely tagged words. A raw, untagged `Int64`
// value's low bit is not a reliable tag — a plain odd i64 would be
// misread as "boxed" and `as_bigint` would dereference garbage. Codegen is
// responsible for routing `Kind::Int64` (never boxed) through the plain
// `cantor_set_*_i64` family instead, exactly as it already does for scalar
// `ensure_tagged`/`ensure_raw_int64`.
#[derive(Default)]
pub struct CantorTaggedIntSet {
    elements: Vec<i64>,
}

impl CantorTaggedIntSet {
    pub fn insert(&mut self, val: i64) {
        match self
            .elements
            .binary_search_by(|probe| tagged_cmp(*probe, val))
        {
            Ok(_) => {}
            Err(pos) => self.elements.insert(pos, val),
        }
    }

    pub fn contains(&self, val: i64) -> bool {
        self.elements
            .binary_search_by(|probe| tagged_cmp(*probe, val))
            .is_ok()
    }

    pub fn size(&self) -> i64 {
        self.elements.len() as i64
    }

    pub fn get(&self, idx: i64) -> i64 {
        self.elements[idx as usize]
    }

    /// Arena deep-copy (see `deep_copy.rs`): a plain `.clone()` of
    /// `elements` would copy boxed elements' *pointer values* verbatim,
    /// leaving them dangling once the arena that owns the pointees resets —
    /// re-box each boxed element into whatever arena is current instead.
    pub(crate) fn arena_deep_copy(&self) -> Self {
        CantorTaggedIntSet {
            elements: self
                .elements
                .iter()
                .map(|&w| deep_copy_tagged_int(w))
                .collect(),
        }
    }
}

/// Deep-copy a tagged `Int` word (see `bigint.rs`'s module doc for the
/// tagging scheme) across an arena-reset boundary: a small (inline) word has
/// no pointee and passes through unchanged; a boxed word's referenced
/// `BigInt` is cloned and re-boxed into whatever arena is current.
///
/// Only ever call this on a genuinely tagged word — see `CantorTaggedIntSet`'s
/// doc comment on why a raw, untagged `Int64` value's low bit can't be
/// trusted as a tag.
pub(crate) fn deep_copy_tagged_int(word: i64) -> i64 {
    if word & 1 == 0 {
        word
    } else {
        let ptr = (word & !1) as *const CantorBigInt;
        let v = unsafe { (*ptr).0.clone() };
        box_bigint(v)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_tagged_set_new_i64() -> i64 {
    crate::arena::alloc(CantorTaggedIntSet::default())
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_tagged_set_insert_i64(set: i64, val: i64) {
    unsafe { &mut *(set as *mut CantorTaggedIntSet) }.insert(val);
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_tagged_set_contains_i64(set: i64, val: i64) -> i64 {
    unsafe { &*(set as *const CantorTaggedIntSet) }.contains(val) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_tagged_set_size_i64(set: i64) -> i64 {
    unsafe { &*(set as *const CantorTaggedIntSet) }.size()
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_tagged_set_get_i64(set: i64, idx: i64) -> i64 {
    unsafe { &*(set as *const CantorTaggedIntSet) }.get(idx)
}
