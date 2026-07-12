use super::helpers::*;

// ── `char(n)` construction ────────────────────────────────────────────────────

#[test]
fn char_constructor_ascii_literal_proved() {
    // A literal ASCII codepoint is trivially in range.
    proved(
        "
letter : -> Char
letter() = char(65)
",
    );
}

#[test]
fn char_constructor_max_valid_codepoint_proved() {
    // 0x10FFFF — the lexer has no hex-literal syntax yet, decimal only.
    proved(
        "
top : -> Char
top() = char(1114111)
",
    );
}

#[test]
fn char_constructor_above_max_codepoint_counterexample() {
    // 0x110000 — one past the top of the Unicode scalar range.
    counterexample(
        "
bad : -> Char
bad() = char(1114112)
",
    );
}

#[test]
fn char_constructor_surrogate_counterexample() {
    // 0xD800 — the first UTF-16 surrogate, not a valid scalar value.
    counterexample(
        "
bad : -> Char
bad() = char(55296)
",
    );
}

#[test]
fn char_constructor_last_surrogate_counterexample() {
    // 0xDFFF — the last UTF-16 surrogate.
    counterexample(
        "
bad : -> Char
bad() = char(57343)
",
    );
}

#[test]
fn char_constructor_just_below_surrogate_range_proved() {
    // 0xD7FF
    proved(
        "
letter : -> Char
letter() = char(55295)
",
    );
}

#[test]
fn char_constructor_just_above_surrogate_range_proved() {
    // 0xE000
    proved(
        "
letter : -> Char
letter() = char(57344)
",
    );
}

#[test]
fn char_constructor_negative_counterexample() {
    counterexample(
        "
bad : -> Char
bad() = char(-1)
",
    );
}

#[test]
fn char_constructor_from_unconstrained_param_counterexample() {
    // n : Int is unconstrained — a counterexample codepoint (e.g. -1) exists,
    // so this is a solver-provable violation, not merely `Unknown`. Step 2
    // (codegen) still needs a runtime range-check trap for this call, since
    // codegen can't rely on every unproved case resolving to a compile-time
    // Counterexample the way this particular predicate always does (linear
    // integer arithmetic is decidable) — see docs/design-decisions.md §13.
    counterexample(
        "
mk : Int -> Char
mk(n) = char(n)
",
    );
}

// ── `Char` is disjoint from `Int` ─────────────────────────────────────────────

#[test]
fn char_identity_proved() {
    proved(
        "
id : Char -> Char
id(c) = c
",
    );
}

#[test]
fn plain_int_is_not_a_char_counterexample() {
    // A bare Int literal, not wrapped with char(), is never a Char.
    counterexample(
        "
bad : -> Char
bad() = 65
",
    );
}

// ── `from(c)` destructor ──────────────────────────────────────────────────────

#[test]
fn char_from_roundtrip_proved() {
    proved(
        "
codepoint : Char -> Int
codepoint(c) = from(c)
",
    );
}

// Note: `from(char(65))` is *not* provably `65` — `mk_Char`/`from_Char` are
// free uninterpreted functions with no inverse axiom, so the solver can't
// derive a round-trip identity for a literal. Confirmed this is a
// pre-existing characteristic of the `distinct` encoding in general (not
// something new to `Char`): `from(litre(5))` isn't provably `5` either.
// Not tested here since it'd just be asserting a known solver limitation.
