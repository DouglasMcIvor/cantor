use super::helpers::*;

// ── Alias sets in domain/range ────────────────────────────────────────────────

#[test]
fn alias_set_literal_in_range_proved() {
    proved(
        "
Colour = {1, 2, 3}
red : -> Colour
red() = 1
",
    );
}

#[test]
fn alias_set_literal_in_range_counterexample() {
    counterexample(
        "
Colour = {1, 2, 3}
bad_colour : -> Colour
bad_colour() = 4
",
    );
}

#[test]
fn alias_named_set_in_domain_proved() {
    proved(
        "
MyNat = alias Nat
inc : MyNat -> MyNat
inc(x) = x + 1
",
    );
}

#[test]
fn alias_named_set_in_domain_counterexample() {
    counterexample(
        "
MyNat = alias Nat
negate : MyNat -> MyNat
negate(x) = -x
",
    );
}

#[test]
fn alias_union_in_range_proved() {
    proved(
        "
SmallPrime = {2, 3, 5, 7}
val : -> SmallPrime
val() = 5
",
    );
}

#[test]
fn transitive_alias_proved() {
    proved(
        "
Inner = {10, 20}
Outer = alias Inner
f : -> Outer
f() = 10
",
    );
}

// ── Distinct sets ─────────────────────────────────────────────────────────────

#[test]
fn distinct_set_identity_proved() {
    // x ∈ Litre → x ∈ Litre: identity function is proved
    proved(
        "
Litre = distinct Nat
volume : Litre -> Litre
volume(x) = x
",
    );
}

#[test]
fn distinct_set_constructor_proved() {
    // litre(n) ∈ Litre when n ∈ Nat
    proved(
        "
Litre = distinct Nat
wrap : Nat -> Litre
wrap(n) = litre(n)
",
    );
}

#[test]
fn distinct_set_from_proved() {
    // from(litre(n)) ∈ Nat — the result is constrained to the basis
    proved(
        "
Litre = distinct Nat
unwrap : Litre -> Nat
unwrap(x) = from(x)
",
    );
}

#[test]
fn distinct_set_range_without_constructor_counterexample() {
    // 273 is a plain integer, not wrapped with kelvin(); solver rejects it
    counterexample(
        "
Kelvin = distinct NatPos
freeze : -> Kelvin
freeze() = 273
",
    );
}

// check_sig (pure expression body) used to lack the `from_D` decode step that
// check_block_sig already had, so a distinct-sorted parameter's counterexample
// witness fell through to `integer_value` on the raw uninterpreted-sort term —
// which never parses as an integer, so `unwrap_or(0)` silently displayed 0
// regardless of the real witness. `from(x) + 5` forces a non-zero witness
// (from(x) = -5) so a wrong-but-plausible `x = 0` display can't hide behind
// a coincidentally-zero answer.
#[test]
fn distinct_set_param_counterexample_shows_decoded_witness() {
    let results = check(
        "
Litre = distinct Int
f : Litre -> NatPos
f(x) = from(x) + 5
",
    );
    let (label, result) = &results[0];
    match result {
        CheckResult::Counterexample { params, .. } => {
            assert_eq!(
                params.get("x"),
                Some(&-5),
                "expected decoded witness x = -5, got {params:?}"
            );
        }
        other => panic!("`{label}` should be Counterexample, got {other:?}"),
    }
}

#[test]
fn distinct_set_wrong_basis_counterexample() {
    // Claiming Int output is Litre (distinct Nat) when input could be negative
    counterexample(
        "
Litre = distinct Nat
bad : Int -> Litre
bad(x) = litre(x)
",
    );
}

// ── Built-in operator domain checks ──────────────────────────────────────────

#[test]
fn distinct_set_arithmetic_operand_domain() {
    // + requires plain Int operands; Litre is distinct so Litre ∈/ Int.
    counterexample(
        "
Litre = distinct Int
add_volumes : Litre * Litre -> Int
add_volumes(x, y) = x + y
",
    );
}

// A distinct-set value and its basis share a Rust-side Kind but live in
// different solver sorts, so `==` between them cannot be encoded — the honest
// verdict is Unknown (previously an ill-sorted term aborted cvc5).
#[test]
fn distinct_vs_basis_equality_unknown() {
    unknown(
        "
Litre = distinct Int
f : Litre -> Bool
f(x) = x == 3
",
    );
}
