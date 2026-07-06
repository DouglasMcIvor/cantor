//! Well-foundedness check for recursive named-set definitions
//! (src/semantics/wellfounded.rs; docs/recursive-sets-plan.md Phase 0).
//!
//! Before this pass existed, any self-referential `NameDef` (however
//! shaped) would send `kind::set_kind`/`kind::set_sort` into unbounded
//! recursion the moment anything asked for its Kind — a stack overflow, not
//! a diagnostic. Every test below is really checking two things at once:
//! that the compiler no longer hangs/crashes on these inputs, *and* that it
//! reports the right one of the three possible outcomes (permanently
//! ill-founded / well-founded-but-not-yet-implemented / shape not
//! recognized).

use cantor::ast::Item;
use cantor::error::CompileError;
use cantor::parser::parse_file;
use cantor::semantics::elaborate::elaborate;

fn elaborate_err(src: &str) -> CompileError {
    let items: Vec<Item> = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    elaborate(&items).expect_err("expected elaborate to reject this recursive set definition")
}

// ── Permanently ill-founded (no base case anywhere in the cycle) ────────────

#[test]
fn bare_self_reference_is_ill_founded() {
    // `Weird = Weird` — not even a union, pure infinite regress.
    let err = elaborate_err("Weird = Weird\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::IllFoundedRecursiveSet { ref name, .. } if name == "Weird"),
        "expected IllFoundedRecursiveSet for `Weird`, got {err:?}"
    );
}

#[test]
fn product_only_with_no_base_arm_is_ill_founded() {
    // `Tree = Tree * Tree` alone (no `Int` alternative) can never bottom
    // out — the algebraic-datatype analogue of `data Tree = Node Tree Tree`
    // with no `Leaf` case, uninhabited by any finite value.
    let err = elaborate_err("Tree = Tree * Tree\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::IllFoundedRecursiveSet { ref name, .. } if name == "Tree"),
        "expected IllFoundedRecursiveSet for `Tree`, got {err:?}"
    );
}

#[test]
fn mutual_recursion_with_no_base_case_is_ill_founded() {
    // `A = B`, `B = A` — a two-step cycle, neither side ever bottoms out.
    let err = elaborate_err("A = B\nB = A\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::IllFoundedRecursiveSet { .. }),
        "expected IllFoundedRecursiveSet, got {err:?}"
    );
}

// ── Well-founded (tier 1 shape recognized), just not implemented yet ────────
//
// These must NOT be reported as ill-founded — the whole point of the
// "generating sets" fixpoint is to accept exactly these. Recursive-set
// codegen/solver support doesn't exist yet (docs/recursive-sets-plan.md
// phases 1-3), so the outcome is `Unsupported`, not success — but it must
// be *that* specific error, not `IllFoundedRecursiveSet` and not a hang.

#[test]
fn structural_recursion_under_product_is_well_founded_not_yet_implemented() {
    // design-decisions.md §3's own example shape: `BinStr`/`Tree`-style,
    // recursive occurrences guarded by a Cartesian product.
    let err = elaborate_err("Tree = Int | Tree * Tree\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::Unsupported { ref feature, .. } if feature.contains("Tree") && feature.contains("recursive-sets-plan")),
        "expected an Unsupported (not-yet-implemented) error for `Tree`, got {err:?}"
    );
}

#[test]
fn bare_self_reference_arm_alongside_a_base_arm_is_well_founded() {
    // `Weird = Weird | Int` — same shape as `bare_self_reference_is_ill_founded`
    // plus one base arm. Caught as a genuine mistake in the first draft of
    // docs/recursive-sets-plan.md: Cantor's cross-kind unions give *every*
    // arm its own CVC5 constructor regardless of shape (see
    // `build_union_datatype_sort` in src/solver/sort.rs), so a bare
    // self-reference arm is exactly as well-founded as a product-guarded
    // one — this is unary-Nat-shaped (`Peano = Zero | Peano`), not
    // Russell's-barber-shaped. Must NOT be `IllFoundedRecursiveSet`.
    let err = elaborate_err("Weird = Weird | Int\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected well-founded (Unsupported, not IllFoundedRecursiveSet) for `Weird`, got {err:?}"
    );
}

#[test]
fn mutual_recursion_with_a_base_case_is_well_founded() {
    // `Tree = Int | Forest`, `Forest = {} | Tree * Forest` — the
    // Tree/Forest shape from docs/recursive-sets-plan.md §4 (mirroring the
    // cvc5 crate's own `dt_mutual_recursion` integration test).
    let err =
        elaborate_err("Tree = Int | Forest\nForest = {} | Tree * Forest\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::Unsupported { .. }),
        "expected well-founded (Unsupported), got {err:?}"
    );
}

// ── Recursion in a shape tier 1 doesn't recognize ────────────────────────────

#[test]
fn recursion_nested_under_intersection_is_unrecognized() {
    // The reference to `Weird` isn't a bare union arm or product factor —
    // it's nested under `&`. Layer 1 (generic cycle detection) still finds
    // the cycle (so this can't hang), but layer 2 refuses to guess at its
    // well-foundedness rather than silently accepting or rejecting it.
    let err = elaborate_err("Weird = Int | (Weird & Int)\nf : Int -> Int\nf(x) = x");
    assert!(
        matches!(err, CompileError::Unsupported { ref feature, .. } if feature.contains("isn't a bare union arm")),
        "expected an unrecognized-shape Unsupported error, got {err:?}"
    );
}

// ── Ordinary, non-recursive definitions are unaffected ──────────────────────

#[test]
fn ordinary_alias_is_unaffected() {
    let items: Vec<Item> = parse_file("MyNat = Nat\nf : MyNat -> MyNat\nf(x) = x")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(
        elaborate(&items).is_ok(),
        "a plain, non-recursive alias must not be touched by the well-foundedness pass"
    );
}

#[test]
fn ordinary_cross_kind_union_is_unaffected() {
    // Non-recursive cross-kind union (already shipped, tagged-union-ir-plan.md)
    // — must keep working exactly as before.
    let items: Vec<Item> = parse_file("Cross = Int | (Bool * Bool)\nf : Cross -> Int\nf(x) = 0")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(
        elaborate(&items).is_ok(),
        "an ordinary non-recursive cross-kind union must not be touched by this pass"
    );
}
