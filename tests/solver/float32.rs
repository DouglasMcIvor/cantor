//! `Float32`/`FiniteFloat32` (docs/design-decisions.md's `Float32`/
//! `FiniteFloat32` section). Solver step: real cvc5 FloatingPoint theory
//! encoding (`mk_fp_sort(8, 24)`) — literals, `+ - * /` (no widening, stays
//! Float32), unary `neg` (`fp.neg`), comparisons (`fp.lt`-family, real IEEE
//! "unordered with NaN" semantics), and `=`/`!=` (cvc5's native FP equality:
//! a single NaN equivalence class, `+0.0f` distinct from `-0.0f` — NOT IEEE
//! `==`). Codegen isn't implemented yet (a separate, later step).

use super::helpers::*;

// ── Closure: Float32 arithmetic never leaves Float32 ─────────────────────────

#[test]
fn identity_proved() {
    proved(
        r#"
f : Float32 -> Float32
f(x) = x
"#,
    );
}

#[test]
fn addition_stays_float32_proved() {
    // No widening (unlike Int -> Rational) — every Float32 op is closed, so
    // this is trivially provable regardless of overflow-to-infinity.
    proved(
        r#"
f : Float32 * Float32 -> Float32
f(a, b) = a + b
"#,
    );
}

#[test]
fn unary_neg_proved() {
    proved(
        r#"
f : Float32 -> Float32
f(x) = -x
"#,
    );
}

#[test]
fn division_by_possibly_zero_needs_no_obligation_proved() {
    // Unlike Int's `/`, Float32 division is total under IEEE 754
    // (1.0f / 0.0f = infinity32, 0.0f / 0.0f = nan32) — no NonZero-style
    // domain obligation, so this proves with no `require`/`assert` guard.
    proved(
        r#"
f : Float32 * Float32 -> Float32
f(a, b) = a / b
"#,
    );
}

// ── `FiniteFloat32`: a real, provable value-range refinement ─────────────────

#[test]
fn finite_float32_excludes_infinity_and_nan_counterexample() {
    // Float32 includes ±infinity32/nan32, which are not in FiniteFloat32 —
    // a genuine counterexample, not a vacuous domain check.
    counterexample(
        r#"
f : Float32 -> FiniteFloat32
f(x) = x
"#,
    );
}

#[test]
fn finite_float32_identity_proved() {
    proved(
        r#"
f : FiniteFloat32 -> FiniteFloat32
f(x) = x
"#,
    );
}

#[test]
fn finite_float32_can_overflow_to_infinity_counterexample() {
    // Two finite floats can still add to an infinite result (e.g. a very
    // large x + x) — FiniteFloat32 is not closed under +, unlike Float32
    // itself. This is the whole point of the range being provable rather
    // than assumed.
    counterexample(
        r#"
f : FiniteFloat32 -> FiniteFloat32
f(x) = x + x
"#,
    );
}

#[test]
fn finite_float32_can_overflow_to_infinity_but_stays_float32_proved() {
    proved(
        r#"
f : FiniteFloat32 -> Float32
f(x) = x + x
"#,
    );
}

#[test]
fn require_finite_float32_is_a_real_obligation_not_silently_trusted_counterexample() {
    // `require x in FiniteFloat32` is a genuine proof obligation, not a
    // trusted assumption (that's `assume`) — since the domain is
    // unrestricted `Float32`, `x = infinity32` really can violate it, so
    // this must be a counterexample, not a silent pass. Confirms the
    // `require`/membership machinery `NonZeroInt` uses for `/` extends to
    // Float32 with no Float32-specific plumbing (it's generic over Kind)
    // and correctly *rejects* an unproven case rather than vacuously
    // accepting it.
    counterexample(
        r#"
f : Float32 -> FiniteFloat32
f(x) {
    require x in FiniteFloat32
    x
}
"#,
    );
}

// ── `=`/`!=`: SMT-LIB FP equality, not IEEE `==` ──────────────────────────────

#[test]
fn equality_is_reflexive_even_for_nan_proved() {
    // The headline reason Cantor's `=` uses SMT-LIB FP equality rather than
    // IEEE `==`: IEEE defines `NaN == NaN` as false (not even reflexive),
    // which would break `x == x` as a decidable congruence. cvc5's native
    // `=` on FP sort instead treats every NaN as one equivalence class, so
    // this holds for *every* Float32 value including `nan32`.
    proved(
        r#"
f : Float32 -> {true}
f(x) = x == x
"#,
    );
}

#[test]
fn positive_and_negative_zero_are_distinct_proved() {
    // The other half of the same design decision: SMT-LIB FP `=` treats
    // `+0.0`/`-0.0` as distinct values (IEEE `==` says they're equal).
    proved(
        r#"
f : -> {true}
f() = 0.0f != -0.0f
"#,
    );
}

// ── Comparisons: real IEEE "unordered with NaN" semantics ────────────────────

#[test]
fn nan_is_not_less_than_itself_proved() {
    // Unlike `=`, ordered comparisons route to `fp.lt`, which is NOT
    // reflexive for NaN — any comparison touching `nan32` is false.
    proved(
        r#"
f : -> {false}
f() = nan32 < nan32
"#,
    );
}

#[test]
fn float32_set_literal_domain_proved() {
    // `{0.0f, 1.0f}` as a domain restricts x to exactly those two values —
    // exercises `membership::literal_element_predicate`'s `FloatLit` arm
    // (a plain `t == mk_fp(...)`, no round-trip UF needed unlike `Char`).
    proved(
        r#"
f : {0.0f, 1.0f} -> Bool
f(x) = x == 0.0f or x == 1.0f
"#,
    );
}

#[test]
fn ordinary_comparison_proved() {
    proved(
        r#"
f : -> {true}
f() = 1f < 2f
"#,
    );
}
