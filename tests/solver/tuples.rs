use super::helpers::*;

// ── Tuple construction and projection ────────────────────────────────────────

#[test]
fn tuple_proj_sum_proved() {
    proved(
        "g : Int * Int -> Int\n\
         g(t) = t.0 + t.1",
    );
}

#[test]
fn tuple_return_proved() {
    proved(
        "h : Int -> Int * Int\n\
         h(x) = (x, x + 1)",
    );
}

#[test]
fn tuple_identity_proved() {
    proved(
        "id_pair : Int * Int -> Int * Int\n\
         id_pair(t) = (t.0, t.1)",
    );
}

// ── Tuple with constrained element sets ──────────────────────────────────────

#[test]
fn nat_pair_proj_stays_nat() {
    proved(
        "fst : Nat * Nat -> Nat\n\
         fst(t) = t.0",
    );
}

#[test]
fn nat_pair_sum_proved() {
    proved(
        "pair_sum : Nat * Nat -> Nat\n\
         pair_sum(t) = t.0 + t.1",
    );
}

// ── Multi-scalar params still work after param_set_exprs ─────────────────────

#[test]
fn two_scalar_params_unchanged() {
    proved(
        "add : Int * Int -> Int\n\
         add(x, y) = x + y",
    );
}

#[test]
fn nat_two_scalar_params_unchanged() {
    proved(
        "add_nat : Nat * Nat -> Nat\n\
         add_nat(x, y) = x + y",
    );
}

// ── Tuple literal in body ─────────────────────────────────────────────────────

#[test]
fn tuple_literal_range_proved() {
    proved(
        "mk : Int -> Int * Int\n\
         mk(x) = (x, 0)",
    );
}
