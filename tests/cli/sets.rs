use super::helpers::*;

// ── Runtime sets ──────────────────────────────────────────────────────────────

#[test]
fn runtime_set_runs_and_returns_correct_result() {
    // runtime_set.cantor:
    //   sum({2,3,5,7}) = 17
    //   membership checks: 3 in primes (✓) + 4 not in primes (✓) = 2
    //   size({2,3,5,7}) = 4
    //   total = 17 + 2 + 4 = 23
    let out = run_subcommand("runtime_set.cantor");
    assert_eq!(out.code, 0, "expected exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 23"),
        "expected 'main() = 23' in output:\n{}", out.stdout
    );
}

#[test]
fn runtime_set_proves_signature() {
    // `main : -> Int` with a Set(Int) body is now fully proved — the solver
    // models runtime sets as opaque integers and treats membership/size as
    // unconstrained, which is sufficient for an Int return range.
    let out = run_subcommand("runtime_set.cantor");
    assert!(
        out.stdout.contains("  proved  "),
        "expected proved result in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample in output:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  unknown  "),
        "unexpected unknown in output:\n{}", out.stdout
    );
}

// ── Set operations (`+` disjoint union, `^` symmetric difference) ────────────

#[test]
fn set_ops_proof_all_proved() {
    let out = run_file("set_ops_proof.cantor");
    assert_eq!(out.code, 0, "set_ops_proof.cantor should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("3 proved"),
        "expected '3 proved' in summary:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
}

#[test]
fn set_ops_proof_shows_set_op_signatures() {
    let out = run_file("set_ops_proof.cantor");
    assert!(out.stdout.contains("Nat ^ {0} -> NatPos"), "strip_zero sig missing:\n{}", out.stdout);
    assert!(out.stdout.contains("{0} + NatPos -> Nat"), "accept_nat sig missing:\n{}", out.stdout);
}

#[test]
fn set_ops_bad_overlapping_union_gives_counterexample() {
    // {0, 1} + {1, 2} is invalid because 1 is in both sets.
    let out = run_file("set_ops_bad.cantor");
    assert_ne!(out.code, 0, "set_ops_bad.cantor should exit non-zero\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
    assert!(
        !out.stdout.contains("  proved  "),
        "unexpected proved line:\n{}", out.stdout
    );
}

#[test]
fn set_ops_bad_counterexample_mentions_not_disjoint() {
    let out = run_file("set_ops_bad.cantor");
    assert!(
        out.stdout.contains("not disjoint"),
        "expected 'not disjoint' in counterexample message:\n{}", out.stdout
    );
}

#[test]
fn set_ops_run_produces_correct_output() {
    // set_ops_run.cantor: accept_nat(7) + strip_zero(3) = 7 + 3 = 10.
    // Regression test for the TaggedUnion narrow/widen codegen paths that
    // back `+` (forced-disjoint union) at runtime — both at function return
    // and at the call-argument boundary (accept_nat(7) widens the literal
    // into a {0} + NatPos tagged value; `main(x) = x` narrows it back).
    let out = run_subcommand("set_ops_run.cantor");
    assert_eq!(out.code, 0, "set_ops_run.cantor run should exit 0\nstdout: {}\nstderr: {}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("main() = 10"),
        "expected 'main() = 10' in output:\n{}", out.stdout
    );
}

#[test]
fn kleene_disjoint_union_not_disjoint_counterexample() {
    // `validate_disjoint_unions` used to have no `KleeneStar` case, so a `+`
    // nested inside `X*` fell through to the wildcard `_ => None` arm and
    // skipped the disjointness check — `({0} + Nat)*` (0 is in both arms)
    // used to falsely prove.
    let out = run_file("kleene_disjoint_union.cantor");
    assert_ne!(out.code, 0, "kleene_disjoint_union.cantor should exit non-zero:\n{}", out.stdout);
    assert!(
        out.stdout.contains("  counterexample  "),
        "expected counterexample result line:\n{}", out.stdout
    );
    assert!(
        out.stdout.contains("not disjoint"),
        "expected 'not disjoint' in counterexample message:\n{}", out.stdout
    );
}
