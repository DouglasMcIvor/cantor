//! `distinct` over a non-`Int` basis (`Bool`, a tuple, a vector, and a
//! `distinct`-over-`distinct` chain), plus the same-Kind named-union case for
//! a non-`Int` shared Kind — the generalization of `distinct`'s previously
//! Int-only `mk_D`/`from_D` machinery (`solver::preds::build_distinct_preds`)
//! to any single, solver-representable basis Kind
//! (`kind::is_distinct_basis_representable`). See docs/design-decisions.md's
//! `alias`/`distinct` section.
//!
//! Heterogeneous-Kind named-union arms (e.g. `Circle: Nat | Rect: Nat *
//! Nat`) are a separate, still-unimplemented generalization — covered by
//! `named_unions.rs::named_union_tuple_arm_is_rejected_not_yet_implemented`.

use super::helpers::*;

#[test]
fn distinct_bool_basis_constructor_and_from_proved() {
    proved_all(
        "Flag = distinct Bool\n\
         describe : Flag -> Bool\n\
         describe(x) = from(x)\n\
         main : -> Bool\n\
         main() = describe(flag(true))",
    );
}

#[test]
fn distinct_tuple_basis_constructor_and_from_proved() {
    proved_all(
        "Point = distinct (Nat * Nat)\n\
         sum_of : Point -> Nat\n\
         sum_of(p) = from(p).0 + from(p).1\n\
         main : -> Nat\n\
         main() = sum_of(point((3, 4)))",
    );
}

#[test]
fn distinct_vector_basis_constructor_and_from_proved() {
    proved_all(
        "Path = distinct Nat*\n\
         first_len : Path -> Nat\n\
         first_len(p) = len(from(p))\n\
         main : -> Nat\n\
         main() = first_len(path([1, 2, 3]))",
    );
}

#[test]
fn distinct_vector_basis_out_of_range_element_is_counterexample() {
    // `Path`'s basis is `Nat*` — a negative element must fail the basis
    // obligation, exactly like an ordinary `litre(-1)` would for `Nat`.
    counterexample(
        "Path = distinct Nat*\n\
         bad : -> Path\n\
         bad() = path([-1, 2])",
    );
}

#[test]
fn distinct_over_distinct_chain_proved() {
    // `Grapheme`'s basis is `Char`, itself a builtin distinct sort — exercises
    // `build_distinct_preds`'s two-pass registration resolving a basis that
    // references *another* distinct name, and `from`'s Kind rule for both
    // the ordinary Kind-transparent case (`Grapheme`) and the ` Char`/
    // `Signed32`/`Unsigned32` exception (`from` on the inner `Char` value
    // must still produce `Int`, not `Char`).
    proved_all(
        "Grapheme = distinct Char\n\
         codepoint : Grapheme -> Int\n\
         codepoint(g) = from(from(g))\n\
         main : -> Int\n\
         main() = codepoint(grapheme('A'))",
    );
}

#[test]
fn named_union_bool_arms_proved() {
    // Both arms share `Kind::Bool` — `kind::union_if_distinct` dedups them to
    // a bare `Kind::Bool` (no cross-kind tag), so `Flag`'s basis resolves to
    // the plain CVC5 boolean sort. Exercises `sort::set_sort`'s distinct-vs-
    // Bool ordering fix (a distinct set whose basis Kind is `Bool` must not
    // be confused with the builtin `Bool` sort itself).
    proved_all(
        "Flag = distinct (A: Bool | B: Bool)\n\
         describe : Flag -> Bool\n\
         describe(f) = from(f)\n\
         main : -> Bool\n\
         main() = describe(Flag.A(true))",
    );
}

#[test]
fn named_union_vector_arms_same_shape_proved() {
    // Two arms sharing the *same* `Vector(Int)` Kind — `kind::union_if_distinct`
    // dedups them to a bare `Kind::Vector(Int)` (no cross-kind tag), and
    // `sort::set_sort`'s sequence-union arm correctly checks `ls == rs`
    // before deciding cross-kind, so this basis resolves to a plain `Seq
    // Int` sort — exercises `encode_call`'s array-literal-to-sequence
    // coercion for a named-union constructor argument.
    proved_all(
        "Path = distinct (Short: Nat* | Long: Nat*)\n\
         first_len : Path -> Nat\n\
         first_len(p) = len(from(p))\n\
         main : -> Nat\n\
         main() = first_len(Path.Short([1, 2])) + first_len(Path.Long([3, 4, 5]))",
    );
}

#[test]
fn named_union_tuple_arms_same_shape_proved() {
    // Two arms sharing the *identical* `Tuple([Int, Int])` Kind — regression
    // test for the `sort::set_sort` union-arm fix (see
    // `tests/solver/cross_kind_unions.rs::identical_shape_tuple_union_domain_projection_proved`
    // for the plain non-`distinct` version of the same bug). Before the fix,
    // this crashed `cvc5` outright at the constructor call site: `mk_Shape`
    // was wrongly given the identity (plain tuple) sort while `set_sort`
    // reported the basis as a cross-kind datatype sort, so `ApplyUf` handed
    // it a value of the wrong sort — a raw C++-level abort, not even a
    // catchable Rust panic.
    proved_all(
        "Shape = distinct (Small: (Nat * Nat) | Big: (Nat * Nat))\n\
         sum_of : Shape -> Nat\n\
         sum_of(s) = from(s).0 + from(s).1\n\
         main : -> Nat\n\
         main() = sum_of(Shape.Small((3, 4))) + sum_of(Shape.Big((10, 20)))",
    );
}

#[test]
fn distinct_set_basis_is_rejected_not_yet_implemented() {
    // `Set(_)` elements have no structural equality/ordering yet
    // (`kind::is_scalar_word_kind`'s existing restriction) — a `distinct`
    // basis of that Kind must fail loudly at elaboration time, not reach the
    // solver with an unrepresentable sort.
    let items = cantor::parser::parse_file(
        "Bag = distinct Set(Int)\n\
         main : -> Int\n\
         main() = 0",
    )
    .unwrap_or_else(|e| panic!("parse error: {e}"));
    let Err(err) = cantor::solver::check_file(&items, 60_000) else {
        panic!("expected elaboration to reject a Set(_) basis");
    };
    assert!(
        matches!(err, cantor::error::CompileError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
    assert!(
        err.to_string().contains("distinct basis"),
        "expected a clear message naming the unsupported basis: {err}"
    );
}
