//! Constructor patterns (pattern-matching plan, step 4/4): end-to-end CLI
//! behavior for `f(Name.Label(x, ...)) = ...` — see
//! `tests/solver/constructor_patterns.rs` for the proof-level coverage.

use super::helpers::*;

#[test]
fn constructor_pattern_area_runs_correctly() {
    let out = run_subcommand("constructor_pattern_area.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 29"),
        "expected area(Shape.Circle(3)) + area(Shape.Rect((4, 5))) = 9 + 20 = 29:\n{}",
        out.stdout
    );
}
