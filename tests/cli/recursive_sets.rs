//! Recursive named-set definitions (design-decisions.md §3, "Recursive
//! sets"), well-foundedness check only — src/semantics/wellfounded.rs, per
//! docs/recursive-sets-plan.md Phase 0.
//!
//! Before this check existed, every one of these files would either hang or
//! stack-overflow the compiler the moment elaboration tried to resolve the
//! recursive name's Kind. None of these prove the recursive set itself
//! usable yet (Kind/solver/codegen support is future work) — this is purely
//! "reject cleanly instead of crashing," end to end through the CLI.

use super::helpers::*;

#[test]
fn bare_self_reference_rejected_with_clean_diagnostic() {
    let out = run_file("recursive_set_bare_self_ref.cantor");
    assert_ne!(
        out.code, 0,
        "expected non-zero exit\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stderr.contains("cannot verify well-foundedness"),
        "expected a well-foundedness diagnostic on stderr:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
    );
}

#[test]
fn product_only_definition_with_no_base_case_rejected() {
    let out = run_file("recursive_set_no_base_case.cantor");
    assert_ne!(out.code, 0, "expected non-zero exit:\nstdout: {}", out.stdout);
    assert!(
        out.stderr.contains("cannot verify well-foundedness"),
        "expected a well-foundedness diagnostic on stderr:\n{}",
        out.stderr
    );
}

#[test]
fn structural_recursion_reported_as_not_yet_implemented() {
    // Well-founded (accepted by the check) but no downstream support exists
    // yet — must be a clear "not yet supported" message, never a silent
    // pass and never confused with the permanent ill-founded rejection.
    let out = run_file("recursive_set_structural_not_yet_implemented.cantor");
    assert_ne!(out.code, 0, "expected non-zero exit:\nstdout: {}", out.stdout);
    assert!(
        out.stderr.contains("not yet supported")
            && out.stderr.contains("recursive-sets-plan"),
        "expected a not-yet-supported diagnostic pointing at the plan doc:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("cannot verify well-foundedness"),
        "must not be confused with the permanent ill-founded rejection:\n{}",
        out.stderr
    );
    assert!(
        !out.stderr.contains("internal compiler error"),
        "must not be reported as an ICE:\n{}",
        out.stderr
    );
}

#[test]
fn recursion_under_intersection_reported_as_unrecognized_shape() {
    let out = run_file("recursive_set_unrecognized_shape.cantor");
    assert_ne!(out.code, 0, "expected non-zero exit:\nstdout: {}", out.stdout);
    assert!(
        out.stderr.contains("not yet supported")
            && out.stderr.contains("bare union arm"),
        "expected an unrecognized-shape diagnostic on stderr:\n{}",
        out.stderr
    );
}
