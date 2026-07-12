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

#[test]
fn char_from_literal_roundtrip_proved() {
    // `from(char(65)) == 65` — encode_call.rs's `assert_distinct_round_trip`
    // asserts `from_D(mk_D(arg)) == arg` as a ground fact at each `distinct`
    // constructor call site (ex-Char too), giving the solver the inverse
    // link `mk_Char`/`from_Char` otherwise lack as independent free
    // uninterpreted functions. See `set_defs.rs`'s
    // `distinct_set_from_literal_roundtrip_proved` for the general
    // (non-Char) `distinct` case.
    proved(
        "
codepoint_of_a : -> {65}
codepoint_of_a() = from(char(65))
",
    );
}
