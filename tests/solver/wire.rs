//! Round-trip tests for the check-worker wire format.
//!
//! `check_file` runs cvc5 in a subprocess so a wedged solver can be killed
//! (cvc5's own `tlimit` is not always honoured — see the hang notes in
//! docs/design-decisions.md), which means everything it returns has to
//! survive a trip through JSON. These tests pin that: if a future AST or
//! semantic-tree node is added without a `Serialize`/`Deserialize` derive
//! it won't compile, and if one round-trips *lossily* the assertions here
//! catch it.

use cantor::{
    error::CompileError,
    parser::parse_file,
    solver::{CheckOutcome, CheckResult, ConstrainedTree, check_file},
};

use super::helpers::check_all;

fn round_trip<T: serde::Serialize + serde::de::DeserializeOwned>(value: &T) -> T {
    let json = serde_json::to_string(value).expect("serialize");
    serde_json::from_str(&json).expect("deserialize")
}

/// A fully-proved file's `ConstrainedTree` is the payload codegen consumes,
/// so every part of it — raw AST, elaborated tree, and both `Span`-keyed
/// side channels — has to come back intact.
#[test]
fn constrained_tree_round_trips() {
    let src = "\
double : Int -> Int
double(x) = x * 2

use_it : Nat -> Int
use_it(n) = double(n) + 1
";
    let items = parse_file(src).expect("parse");
    let tree = match check_file(&items, 60_000).expect("check") {
        CheckOutcome::Proved(tree) => tree,
        CheckOutcome::NotProved(results) => panic!("expected fully proved, got {results:?}"),
    };

    // Guard the guard: a tree with empty side channels would make the
    // assertions below vacuous.
    assert!(
        !tree.overflow_checks.is_empty(),
        "fixture should exercise the overflow side channel"
    );

    let back: ConstrainedTree = round_trip(&tree);

    assert_eq!(back.items.len(), tree.items.len());
    assert_eq!(back.sem_items.len(), tree.sem_items.len());
    assert_eq!(back.results, tree.results);
    assert_eq!(back.overflow_checks, tree.overflow_checks);
    assert_eq!(back.overload_resolution, tree.overload_resolution);
}

/// `Span` is a struct, and JSON only allows string map keys — the two
/// `HashMap<Span, _>` side channels go through `span_keyed_map` for exactly
/// this reason. Serializing them as a plain map is a runtime error, not a
/// compile error, so it needs a test rather than the type checker.
#[test]
fn span_keyed_side_channels_survive_json() {
    let src = "\
inc : Int -> Int
inc(x) = x + 1
";
    let items = parse_file(src).expect("parse");
    let CheckOutcome::Proved(tree) = check_file(&items, 60_000).expect("check") else {
        panic!("expected fully proved");
    };
    assert!(!tree.overflow_checks.is_empty());

    let back = round_trip(&tree);
    for (span, fits) in &tree.overflow_checks {
        assert_eq!(back.overflow_checks.get(span), Some(fits));
    }
}

/// A counterexample carries rendered witness values in a `HashMap<String,
/// String>` plus the reason text — the part of the report a user actually
/// reads, so it has to cross the process boundary verbatim.
#[test]
fn counterexample_round_trips() {
    let src = "\
bad : Int -> Nat
bad(x) = x - 1
";
    let results = check_all(src);
    let result = &results[0].1[0].1;
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "fixture should produce a counterexample, got {result:?}"
    );
    assert_eq!(&round_trip(result), result);
}

/// ICEs cross the boundary too, and `Ice`'s Rust location is the one field
/// that forced a refactor: `Location::caller()` hands back a `&'static
/// Location`, which has no public constructor to deserialize into.
#[test]
fn ice_location_round_trips() {
    let err = CompileError::ice("something went wrong");
    let back = round_trip(&err);
    assert_eq!(err.to_string(), back.to_string());
    assert!(back.is_ice());
    let CompileError::Ice { rust_location, .. } = &back else {
        panic!("expected Ice");
    };
    assert!(
        rust_location.file.ends_with("wire.rs"),
        "location should point at this test's call site, got {rust_location}"
    );
}
