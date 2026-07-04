use cantor::{
    parser::parse_file,
    solver::{CheckOutcome, ConstrainedTree, check_file},
};

pub use cantor::solver::CheckResult;

/// Parse and fully check `src`, returning the `ConstrainedTree` — panics if
/// the file isn't fully `Proved`. Used by tests that need to inspect
/// tree-level data (e.g. `overflow_checks`) rather than just per-signature
/// `CheckResult`s.
pub fn check_tree(src: &str) -> ConstrainedTree {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    match check_file(&items, 60_000).unwrap_or_else(|e| panic!("check error: {e}")) {
        CheckOutcome::Proved(tree) => tree,
        CheckOutcome::NotProved(results) => panic!("expected file to be fully proved, got: {results:?}"),
    }
}

/// Parse `src`, build the full function environment, and return the results
/// for every function in the file — regardless of whether the file as a
/// whole was fully proved (tests want the per-signature `CheckResult`
/// either way, not the `ConstrainedTree` gate).
pub fn check_all(src: &str) -> Vec<(String, Vec<(String, CheckResult)>)> {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    match check_file(&items, 60_000).unwrap_or_else(|e| panic!("check error: {e}")) {
        CheckOutcome::Proved(tree) => tree.results,
        CheckOutcome::NotProved(results) => results,
    }
}

/// Parse a single-function source, check it, and return its signature results.
pub fn check(src: &str) -> Vec<(String, CheckResult)> {
    let mut all = check_all(src);
    assert_eq!(all.len(), 1, "expected exactly one function");
    all.remove(0).1
}

/// Assert that the first (usually only) signature of a single-function source is Proved.
pub fn proved(src: &str) {
    for (label, result) in &check(src) {
        assert_eq!(result, &CheckResult::Proved, "`{label}` should be Proved, got {result:?}");
    }
}

/// Assert that every signature in a multi-function source is Proved.
pub fn proved_all(src: &str) {
    for (_fn_name, sig_results) in &check_all(src) {
        for (label, result) in sig_results {
            assert_eq!(result, &CheckResult::Proved, "`{label}` should be Proved, got {result:?}");
        }
    }
}

/// Look up one function's first-signature result in a `check_all` report.
pub fn result_for<'a>(
    results: &'a [(String, Vec<(String, CheckResult)>)],
    name: &str,
) -> &'a CheckResult {
    let (_, sig_results) = results
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("no function `{name}` in results"));
    &sig_results[0].1
}

/// Assert that the single-function source produces at least one Counterexample.
pub fn counterexample(src: &str) {
    let results = check(src);
    let (label, result) = results.into_iter().next().unwrap();
    assert!(
        matches!(result, CheckResult::Counterexample { .. }),
        "expected Counterexample for `{label}`, got {result:?}"
    );
}

/// Assert that the single-function source produces at least one Unknown.
pub fn unknown(src: &str) {
    let results = check(src);
    let (label, result) = results.into_iter().next().unwrap();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "expected Unknown for `{label}`, got {result:?}"
    );
}

/// Assert that `src` fails to elaborate/check at all (a whole-file `CompileError`,
/// not a per-signature `Counterexample`/`Unknown`) — e.g. a Kind mismatch the
/// elaborator rejects loudly rather than silently coercing.
pub fn rejected(src: &str) {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(check_file(&items, 60_000).is_err(), "expected `{src}` to fail elaboration/checking");
}
