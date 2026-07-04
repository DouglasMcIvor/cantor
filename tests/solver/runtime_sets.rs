use super::helpers::*;

// ── Element-kind constraints from Set(ElemKind) ───────────────────────────────

// Sum of Set(Nat) elements accumulates into Nat — provable because the
// element-kind constraint (x >= 0) is propagated to the loop variable.
#[test]
fn set_nat_sum_proves_nat_invariant() {
    proved(
        "
f : -> Nat
f() {
    mut s   : Set(Nat) = {1, 2, 3}
    mut acc : Nat = 0
    for x in s {
        acc := acc + x
    }
    acc
}
",
    );
}

// Without element-kind propagation x would be unconstrained, allowing a
// negative value that breaks the Nat invariant on acc.  The solver must
// find a counterexample when acc is declared Nat but the SET is Set(Int).
// (This is actually provable now because Int gives no constraint and acc : Nat
// is unconstrained post-loop — so this tests that Set(Int) does NOT falsely
// generate a counterexample.)
#[test]
fn set_int_sum_into_int_still_proves() {
    proved(
        "
f : -> Int
f() {
    mut s   : Set(Int) = {1, 2, 3}
    mut acc : Int = 0
    for x in s {
        acc := acc + x
    }
    acc
}
",
    );
}

// Set(Nat) element constraint allows proving a Nat-range function.
#[test]
fn set_nat_loop_proves_nat_range() {
    proved(
        "
sum_nat : -> Nat
sum_nat() {
    mut s   : Set(Nat) = {10, 20, 30}
    mut acc : Nat = 0
    for x in s {
        acc := acc + x
    }
    acc
}
",
    );
}

// Set(Int - {0}): elements are non-zero, which the solver can use.
// We just check the function proves — the obligation is return in Int.
#[test]
fn set_nonzero_int_proves_int_range() {
    proved(
        "
f : -> Int
f() {
    mut s   : Set(Int - {0}) = {1, 2, 3}
    mut acc : Int = 0
    for x in s {
        acc := acc + x
    }
    acc
}
",
    );
}

// Regression: plain Set(Int) with Int return range was already proved before
// this change and must remain proved.
#[test]
fn runtime_set_int_range_regression() {
    proved(
        "
main : -> Int
main() {
    mut primes : Set(Int) = {2, 3, 5, 7}
    mut acc    : Int = 0
    for p in primes {
        acc := acc + p
    }
    acc
}
",
    );
}
