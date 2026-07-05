//! Canonical built-in named-set registry.
//!
//! Before this module existed, `Int`/`Nat`/`NatPos`/`NonZeroInt`/`Bool`/`Fail`/
//! `Int8`..`Int64` were each independently string-matched in four places:
//! `kind::set_kind`, `solver::membership`, `codegen::membership`, and
//! `solver::sort`. Each one risked drifting out of sync with the others.
//! This module is the one place a built-in name maps to its `Kind` and (for
//! integer-kinded sets) its value bound; each backend still encodes that bound
//! in its own native form (a CVC5 term vs an LLVM `icmp`), since that encoding
//! is genuinely backend-specific.

use crate::kind::Kind;

/// The value-range predicate for an integer-kinded built-in set.
/// Meaningless for non-`Kind::Int` builtins (`Bool`, `Fail`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntBound {
    /// All of `Int` — no constraint beyond "is an integer".
    Any,
    /// `x >= 0`
    NonNeg,
    /// `x > 0`
    Positive,
    /// `x != 0`
    NonZero,
    /// `min <= x <= max`
    Bounded(i64, i64),
    /// `x < min || x > max` — the complement of `Bounded(min, max)`. Only
    /// user today: `BigInt = Int - Int64` (`Outside(i64::MIN, i64::MAX)`),
    /// exposed so `assert`/`require ... not in BigInt` work as an ordinary
    /// named-set check — see int-soundness-plan.md phase 3.
    Outside(i64, i64),
}

// `Kind` dropped `Copy` when `Tuple(Vec<Kind>)` was added, so `BuiltinSet` can
// only be `Clone` — every variant used here (`Int`/`Bool`/`Fail`) is cheap to
// clone regardless.
#[derive(Debug, Clone)]
pub struct BuiltinSet {
    pub kind: Kind,
    /// Only meaningful when `kind == Kind::Int`.
    pub bound: IntBound,
}

/// Look up a built-in set by name. Returns `None` for user-defined names,
/// which callers resolve through `NameDefs` instead.
pub fn lookup(name: &str) -> Option<BuiltinSet> {
    let int = |bound| {
        Some(BuiltinSet {
            kind: Kind::Int,
            bound,
        })
    };
    match name {
        "Bool" => Some(BuiltinSet {
            kind: Kind::Bool,
            bound: IntBound::Any,
        }),
        "Fail" => Some(BuiltinSet {
            kind: Kind::Fail,
            bound: IntBound::Any,
        }),
        "Int" => int(IntBound::Any),
        "Nat" => int(IntBound::NonNeg),
        "NatPos" => int(IntBound::Positive),
        "NonZeroInt" => int(IntBound::NonZero),
        "Int8" => int(IntBound::Bounded(i8::MIN as i64, i8::MAX as i64)),
        "Int16" => int(IntBound::Bounded(i16::MIN as i64, i16::MAX as i64)),
        "Int32" => int(IntBound::Bounded(i32::MIN as i64, i32::MAX as i64)),
        "Int64" => int(IntBound::Bounded(i64::MIN, i64::MAX)),
        // int-soundness-plan phase 3: `Int - Int64` — the part of `Int` a
        // raw `i64` word can't represent, backed by a boxed `CantorBigInt`
        // at runtime (see runtime/mod.rs). A named set purely for
        // `in`/`not in` checks (e.g. `assert x not in BigInt`); it plays no
        // role in the `Kind::Int64` split/promotion machinery itself, which
        // reasons about `Int64` directly.
        "BigInt" => int(IntBound::Outside(i64::MIN, i64::MAX)),
        _ => None,
    }
}
