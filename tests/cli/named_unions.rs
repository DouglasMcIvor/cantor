//! Named union sets (pattern matching, step 3/4): end-to-end CLI behavior
//! for auto-generated per-arm constructors (`Shape.Circle`, `Shape.Radius`).

use super::helpers::*;

#[test]
fn named_union_constructor_runs_correctly() {
    // Labeled arms are always tag-forced now (see
    // `parser::items::parse_distinct_value`), even when every arm shares a
    // Kind — see `tests/solver/named_unions.rs::
    // named_union_same_kind_labels_stay_distinct_proved` for the
    // distinctness proof. This test only checks that both labeled
    // constructors compile and run without crashing (`show()`'s output
    // doesn't expose the label, so it can't demonstrate distinctness here).
    let out = run_subcommand("named_union_shape.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 34"),
        "expected show(Shape.Circle(3)) ++ show(Shape.Radius(4)) = \"34\":\n{}",
        out.stdout
    );
}
