//! MVP IO event loop (docs/design-decisions.md §6) — `main`-shape validation.
//! `src/solver/event_loop.rs` is a structural check, not a proof obligation,
//! so failures surface as a whole-file `CompileError` (`rejected`), not a
//! per-signature `Counterexample`/`Unknown`.

use super::helpers::*;

#[test]
fn well_formed_event_loop_main_is_proved() {
    proved_all(
        "Counter = alias Nat\n\
         main : Char* * Counter -> Char* * Counter\n\
         main(event, state) = (event, state)\n\
         main : -> Counter\n\
         main() = 0",
    );
}

#[test]
fn missing_seed_overload_is_rejected() {
    rejected(
        "Counter = alias Nat\n\
         main : Char* * Counter -> Char* * Counter\n\
         main(event, state) = (event, state)",
    );
}

#[test]
fn mismatched_state_identifiers_are_rejected() {
    rejected(
        "Counter = alias Nat\n\
         Other = alias Nat\n\
         main : Char* * Counter -> Char* * Other\n\
         main(event, state) = (event, 0)\n\
         main : -> Counter\n\
         main() = 0",
    );
}

#[test]
fn seed_with_mismatched_state_identifier_is_rejected() {
    rejected(
        "Counter = alias Nat\n\
         Other = alias Nat\n\
         main : Char* * Counter -> Char* * Counter\n\
         main(event, state) = (event, state)\n\
         main : -> Other\n\
         main() = 0",
    );
}

#[test]
fn anonymous_state_set_expression_is_rejected() {
    // `{0, 1, 2}` used inline (not via a named alias) can't be checked for
    // identifier equality between domain and range, so it's rejected up
    // front rather than silently accepted as "probably fine."
    rejected(
        "main : Char* * {0, 1, 2} -> Char* * {0, 1, 2}\n\
         main(event, state) = (event, state)\n\
         main : -> {0, 1, 2}\n\
         main() = 0",
    );
}

#[test]
fn unrelated_two_arity_main_is_left_alone() {
    // Not `Char* * S -> Char* * S`-shaped at all — an ordinary function that
    // happens to be named `main`. The event-loop check must not fire.
    proved_all(
        "main : Int * Int -> Int\n\
         main(x, y) = x + y",
    );
}

#[test]
fn two_arity_main_with_non_char_star_output_is_left_alone() {
    proved_all(
        "main : Int * Int -> Int * Int\n\
         main(x, y) = (x, y)",
    );
}
