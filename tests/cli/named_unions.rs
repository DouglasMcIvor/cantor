//! Named union sets (pattern matching, step 3/4): end-to-end CLI behavior
//! for auto-generated per-arm constructors (`Shape.Circle`, `Shape.Radius`).

use super::helpers::*;

#[test]
fn named_union_constructor_runs_correctly() {
    let out = run_subcommand("named_union_shape.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 7"),
        "expected describe(Shape.Circle(3)) + describe(Shape.Radius(4)) = 3 + 4 = 7:\n{}",
        out.stdout
    );
}
