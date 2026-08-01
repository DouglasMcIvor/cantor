//! Exact rational arithmetic — the runtime half of the numeric tower
//! (docs/rational-plan.md).
//!
//! Representation: a `Rational` value is a plain arena pointer-as-i64 to a
//! `CantorRational`. Deliberately *not* the tagged small/boxed scheme
//! `bigint.rs` uses for `Int`: there is no useful "small rational" that fits
//! in 63 bits, and `Int` already covers the case where a rational happens to
//! be a whole number (the compiler narrows through `cantor_rational_to_int`
//! once the solver has proved integrality). So the pointer is never tagged
//! and its low bit carries no meaning.
//!
//! `num_rational::BigRational` keeps every value normalized — gcd-reduced,
//! denominator positive — so `3/2 * 2/3` is `1/1` and equality is structural.
//! That is what makes `cantor_rational_eq` meaningful: two independent
//! allocations holding the same number compare equal, which pointer identity
//! would get wrong.
//!
//! Exactness means none of these operations can overflow, which is why
//! `solver::encode` emits no `Int64`-fit obligation for a Rational-sorted
//! node.

use num_rational::BigRational;

#[repr(align(8))]
pub struct CantorRational(BigRational);

fn box_rational(v: BigRational) -> i64 {
    crate::arena::alloc(CantorRational(v))
}

fn as_rational(word: i64) -> BigRational {
    let ptr = word as *const CantorRational;
    unsafe { (*ptr).0.clone() }
}

/// Widen a tagged `Int` word into a `Rational` — the ℤ ⊂ ℚ coercion, emitted
/// by codegen at every widening boundary (call argument, function return,
/// `if`-branch merge, mixed-operand arithmetic).
#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_from_int(word: i64) -> i64 {
    box_rational(BigRational::from(crate::bigint::as_bigint(word)))
}

/// Narrow a `Rational` back to a tagged `Int` word.
///
/// Aborts (rather than truncating) when the value isn't a whole number. This
/// is only ever emitted where the solver proved integrality, or immediately
/// after a `cantor_rational_is_integer` guard, so reaching the failure branch
/// means a proof was wrong — a compiler bug, not a legitimate runtime
/// outcome. Aborts rather than panics for the same reason
/// `cantor_bigint_to_i64` does: a Rust panic cannot safely unwind across the
/// `extern "C"` boundary into JIT-compiled code.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_to_int(word: i64) -> i64 {
    let r = as_rational(word);
    if !r.is_integer() {
        eprintln!(
            "cantor_rational_to_int: {r} is not a whole number despite a proved Int \
             boundary — compiler invariant violated"
        );
        std::process::exit(1);
    }
    crate::bigint::encode_bigint(r.to_integer())
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_add(a: i64, b: i64) -> i64 {
    box_rational(as_rational(a) + as_rational(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_sub(a: i64, b: i64) -> i64 {
    box_rational(as_rational(a) - as_rational(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_mul(a: i64, b: i64) -> i64 {
    box_rational(as_rational(a) * as_rational(b))
}

/// Divisor-nonzero is a hard proof obligation established before codegen
/// emits this call (`solver::obligations`' `NonZeroRational` domain on `/`'s
/// second argument), so this never defends against a zero divisor — same
/// contract as `cantor_bigint_div`.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_div(a: i64, b: i64) -> i64 {
    box_rational(as_rational(a) / as_rational(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_neg(a: i64) -> i64 {
    box_rational(-as_rational(a))
}

/// Three-way comparison: -1 (`a < b`), 0 (`a == b`), 1 (`a > b`).
///
/// This backs `==`/`!=` as well as the ordered comparisons — normalization
/// means `cmp == 0` *is* value equality, so there is no separate `eq` entry
/// point. Comparing the pointers instead would be wrong: two allocations can
/// hold the same number.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_cmp(a: i64, b: i64) -> i64 {
    use std::cmp::Ordering;
    match as_rational(a).cmp(&as_rational(b)) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

/// The decimal rendering shared by `show` and CLI output: `num/den`, or just
/// `num` when the value is a whole number. Normalization means `4/2` prints
/// as `2` and `-1/-2` as `1/2`.
pub fn format_rational(r: &BigRational) -> String {
    if r.is_integer() {
        r.to_integer().to_string()
    } else {
        format!("{}/{}", r.numer(), r.denom())
    }
}

/// `show(q)` — renders as a `Char*` (`Vector(Char)`) value, same packaging as
/// `cantor_show_bigint`.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_show_rational(word: i64) -> i64 {
    crate::event_loop::encode_char_star(&format_rational(&as_rational(word)))
}

/// Renders as a heap-allocated null-terminated C string, for the CLI's
/// top-level result display — mirrors `cantor_bigint_to_string`.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_rational_to_string(word: i64) -> i64 {
    let s = format_rational(&as_rational(word));
    let c_string = std::ffi::CString::new(s).expect("rational decimal string has no interior NUL");
    c_string.into_raw() as i64
}
