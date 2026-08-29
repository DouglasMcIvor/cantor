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

/// Name of the built-in `Set(X)` power-set constructor. It's a parametrized
/// compile-time function rather than a plain named set, so it can't go
/// through `lookup` (which only takes a bare name) — this constant is the
/// single source of truth every `callee.0 == "Set"` check compares against,
/// so the three call sites (`kind::set_kind`, `semantics::elaborate`,
/// `solver::loops`'s runtime-set-variable detection) can't drift apart on
/// the spelling.
pub const SET_CONSTRUCTOR: &str = "Set";

/// The value-range predicate for a numeric built-in set. `Kind::Int` uses
/// every variant; `Kind::Rational` uses only `Any` and `NonZero` (see
/// `lookup`'s `Rational` entry). Meaningless for the non-numeric builtins
/// (`Bool`, `Fail`, `None`, `Char`, `Signed32`, `Unsigned32`, `Float32`/
/// `FiniteFloat32` — the latter two use `FloatBound` instead, below).
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

/// The value-range predicate for `Kind::Float32`. A separate enum from
/// `IntBound` rather than a shoehorned variant of it — "excludes
/// ±infinity/NaN" isn't a numeric bound in any sense `IntBound::Bounded`/
/// `Outside` share, it's a finiteness predicate — see `solver::membership`'s
/// `Var("FiniteFloat32")` arm for the actual `fp.isInfinite`/`fp.isNaN`
/// encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatBound {
    /// All of `Float32`, including `±infinity32`/`nan32`.
    Any,
    /// Excludes `±infinity32`/`nan32` — `FiniteFloat32`.
    Finite,
}

// `Kind` dropped `Copy` when `Tuple(Vec<Kind>)` was added, so `BuiltinSet` can
// only be `Clone` — every variant used here (`Int`/`Bool`/`Fail`) is cheap to
// clone regardless.
#[derive(Debug, Clone)]
pub struct BuiltinSet {
    pub kind: Kind,
    /// Only meaningful when `kind == Kind::Int` or `Kind::Rational`.
    pub bound: IntBound,
    /// Only meaningful when `kind == Kind::Float32`.
    pub float_bound: FloatBound,
}

/// Look up a built-in set by name. Returns `None` for user-defined names,
/// which callers resolve through `NameDefs` instead.
pub fn lookup(name: &str) -> Option<BuiltinSet> {
    let int = |bound| {
        Some(BuiltinSet {
            kind: Kind::Int,
            bound,
            float_bound: FloatBound::Any,
        })
    };
    match name {
        "Bool" => Some(BuiltinSet {
            kind: Kind::Bool,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        "Fail" => Some(BuiltinSet {
            kind: Kind::Fail,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        "None" => Some(BuiltinSet {
            kind: Kind::None,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
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
        // Wrapping fixed-width integers (docs/wrapping-and-quotient-sets-
        // plan.md, Feature 1) — genuinely distinct sorts, not `Int` subsets,
        // so `bound` is meaningless here (`IntBound::Any` is filler, same as
        // the `Bool`/`Fail` entries above).
        "Signed32" => Some(BuiltinSet {
            kind: Kind::Signed32,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        "Unsigned32" => Some(BuiltinSet {
            kind: Kind::Unsigned32,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        // ℚ — the one builtin family that is a strict *superset* of `Int`
        // rather than a subset or a disjoint sort. Membership of an
        // integer-sorted term is trivially true; the interesting direction is
        // the other way (`IsInteger`), which `solver::membership` handles
        // under the `Int` names above. See docs/rational-plan.md.
        //
        // `NonZeroRational` is what a *total* rational division's divisor
        // domain is spelled as — `NonZeroInt`'s counterpart one level up the
        // tower, and the domain `solver::obligations` uses for `/` at every
        // Kind (on an integer-sorted term the two produce the identical
        // `t != 0` predicate, so nothing regressed for integer division).
        // `Nat`/`NatPos` have no ℚ analogue yet: shipped on demand rather
        // than speculatively, and `solver::membership`'s `Rational` arm
        // reports `Unsupported` rather than guessing if one ever appears.
        "Rational" => Some(BuiltinSet {
            kind: Kind::Rational,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        "NonZeroRational" => Some(BuiltinSet {
            kind: Kind::Rational,
            bound: IntBound::NonZero,
            float_bound: FloatBound::Any,
        }),
        // A Unicode scalar value — a builtin *distinct* sort (like `Fail`),
        // not an `Int` subset, so `bound` is meaningless filler here too.
        // Unlike Signed32/Unsigned32, not every `Int` is a valid `Char`;
        // validity (`0..=0x10FFFF`, excluding surrogates) is a proof
        // obligation checked once at `char(n)` construction, not encoded via
        // `IntBound`. See docs/design-decisions.md §13.
        "Char" => Some(BuiltinSet {
            kind: Kind::Char,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        // IEEE 754 binary32 — `FiniteFloat32` is a value-range refinement of
        // the same `Kind::Float32` (excludes `±infinity32`/`nan32`), not a
        // second sort, mirroring `Nat`/`Int` above rather than `Signed32`/
        // `Unsigned32`. `bound` is meaningless filler here (`Kind::Float32`,
        // not `Kind::Int`); `float_bound` carries the real predicate. See
        // docs/design-decisions.md's `Float32`/`FiniteFloat32` section.
        "Float32" => Some(BuiltinSet {
            kind: Kind::Float32,
            bound: IntBound::Any,
            float_bound: FloatBound::Any,
        }),
        "FiniteFloat32" => Some(BuiltinSet {
            kind: Kind::Float32,
            bound: IntBound::Any,
            float_bound: FloatBound::Finite,
        }),
        _ => None,
    }
}
