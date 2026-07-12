use super::helpers::*;

// ── Kleene-star vectors (X* via sequence theory) ─────────────────────────────

#[test]
fn vectors_kleene_demo_all_proved() {
    let out = run_file("vectors_kleene_demo.cantor");
    assert_eq!(
        out.code, 0,
        "vectors_kleene_demo.cantor should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}",
        out.stdout
    );
}

// ── Kleene-star vectors: Arrow runtime (Int* and Bool*) ──────────────────────

#[test]
fn vectors_runtime_all_proved() {
    let out = run_file("vectors_runtime.cantor");
    assert_eq!(
        out.code, 0,
        "vectors_runtime.cantor check should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_runtime_run_returns_len_of_composed_vector() {
    // main() = get_len(identity_int(make_int_vec())) = len([1,2,3]) = 3
    let out = run_subcommand("vectors_runtime.cantor");
    assert_eq!(
        out.code, 0,
        "vectors_runtime.cantor run should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        out.stdout.contains("3"),
        "expected output 3 (len of [1,2,3]):\n{}",
        out.stdout
    );
}

// ── Vectors: repeated products and array literals ─────────────────────────────

#[test]
fn vectors_demo_all_proved() {
    let out = run_file("vectors_demo.cantor");
    assert_eq!(
        out.code, 0,
        "vectors_demo.cantor should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_demo_run_produces_correct_output() {
    let out = run_subcommand("vectors_demo.cantor");
    assert_eq!(
        out.code, 0,
        "vectors_demo.cantor run should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        out.stdout.contains("6"),
        "expected output 6 from sum3(1,2,3):\n{}",
        out.stdout
    );
}

// ── Set difference in vector domains ─────────────────────────────────────────
//
// Previously panicked: `Nat* - A` was misparsed as `Nat * (-A)` (unary negation),
// causing an unreachable! in set_sort. Now parsed correctly as KleeneStar(Nat) Sub A.

#[test]
fn vec_domain_set_diff_empty_set_counterexample() {
    // `(Nat* - {})` is just `Nat*` (empty set subtracted is a no-op).
    // `first_elem(xs) = xs[0]` gets a counterexample because xs could be empty.
    let out = run_file("vec_set_diff_domain.cantor");
    assert!(
        !out.stderr.contains("panicked"),
        "should not panic:\n{}",
        out.stderr
    );
    assert!(
        out.stdout.contains("counterexample"),
        "expected counterexample for first_elem:\n{}",
        out.stdout
    );
}

#[test]
fn vec_domain_set_diff_named_set_counterexample() {
    // `(Nat* - Nat)` — sequences are disjoint from integers; effectively `Nat*`.
    // Also gets a counterexample (empty vector).
    let out = run_file("vec_set_diff_domain.cantor");
    assert!(
        !out.stderr.contains("panicked"),
        "should not panic:\n{}",
        out.stderr
    );
    let lines: Vec<&str> = out.stdout.lines().collect();
    let ce_lines: Vec<&&str> = lines
        .iter()
        .filter(|l| l.contains("counterexample"))
        .collect();
    assert!(
        ce_lines.len() >= 2,
        "expected counterexample for both first_elem and first_elem2:\n{}",
        out.stdout
    );
}

#[test]
fn vec_domain_set_diff_pass_through_proved() {
    // `pass_through : (Nat* - {}) -> Nat*` — identity on the same domain/range is proved.
    let out = run_file("vec_set_diff_domain.cantor");
    assert!(
        out.stdout.contains("proved"),
        "expected pass_through to be proved:\n{}",
        out.stdout
    );
}

// ── Sequence unification: scalar/tuple ↔ vector boxing ───────────────────────

#[test]
fn vec_scalar_return_proved() {
    // `foo : -> Nat*; foo() = 5` — scalar 5 is the length-1 sequence [5]; proved.
    let out = run_file("vec_scalar_box.cantor");
    assert!(
        out.stdout.contains("proved          foo"),
        "expected foo proved:\n{}",
        out.stdout
    );
}

#[test]
fn vec_scalar_call_arg_proved() {
    // `val() = get(5)` where get expects Nat* — proved because 5 ∈ Nat* - {[]}.
    let out = run_file("vec_scalar_box.cantor");
    assert!(
        out.stdout.contains("proved          val"),
        "expected val proved:\n{}",
        out.stdout
    );
}

#[test]
fn vec_scalar_box_runs_len_1() {
    // JIT: `main() = len(foo())` where `foo() = 5 : Nat*` — length is 1.
    let out = run_subcommand("vec_scalar_box.cantor");
    assert_eq!(out.code, 0, "should exit 0:\n{}", out.stderr);
    assert!(
        out.stdout.contains("main() = 1"),
        "expected len 1:\n{}",
        out.stdout
    );
}

#[test]
fn vec_tuple_box_return_proved() {
    // `pair : -> Nat*; pair() = (3, 4)` — tuple (3,4) is the length-2 sequence [3,4]; proved.
    let out = run_file("vec_tuple_box.cantor");
    assert!(
        out.stdout.contains("proved          pair"),
        "expected pair proved:\n{}",
        out.stdout
    );
}

#[test]
fn vec_tuple_box_runs_len_2() {
    // JIT: `main() = len(pair())` where `pair() = (3, 4) : Nat*` — length is 2.
    let out = run_subcommand("vec_tuple_box.cantor");
    assert_eq!(out.code, 0, "should exit 0:\n{}", out.stderr);
    assert!(
        out.stdout.contains("main() = 2"),
        "expected len 2:\n{}",
        out.stdout
    );
}

#[test]
fn vec_length_narrowing_h_proved() {
    // `h : (Nat* - Nat - {[]}) -> Nat` — domain length ≥ 2 discharges xs[0] and xs[1].
    let out = run_file("vec_length_narrowing.cantor");
    assert!(
        out.stdout.contains("proved          h :"),
        "expected h proved:\n{}",
        out.stdout
    );
}

#[test]
fn vec_length_narrowing_control_counterexample() {
    // `h_no_empty_guard : (Nat* - Nat) -> Nat` — length ≠ 1 but empty still allowed → counterexample.
    let out = run_file("vec_length_narrowing.cantor");
    assert!(
        out.stdout.contains("counterexample  h_no_empty_guard"),
        "expected h_no_empty_guard counterexample:\n{}",
        out.stdout
    );
}

// ── Vector iteration (`for x in xs` over `X*`) ───────────────────────────────

#[test]
fn vector_iteration_all_proved() {
    let out = run_file("vector_iteration.cantor");
    assert_eq!(
        out.code, 0,
        "vector_iteration.cantor should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}",
        out.stdout
    );
}

#[test]
fn vector_iteration_run_sums_vector_param() {
    let out = run_subcommand("vector_iteration.cantor");
    assert_eq!(
        out.code, 0,
        "vector_iteration.cantor run should exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 12"),
        "expected 'main() = 12' in output:\n{}",
        out.stdout
    );
}

// ── Kleene-star membership over tuple-sorted terms ───────────────────────────
//
// A local variable with a fixed-arity tuple kind (`Nat * 3`), checked against
// a Kleene-star range (`Nat*`) — `t` here is a tuple-sorted *opaque* SSA
// constant (a local `let`, not an `mk_tuple(...)` literal), which used to
// abort cvc5 raw (`membership_constraint`'s KleeneStar-tuple branch called
// `.child()`, valid only on a genuine constructor application). See
// tests/solver/vectors.rs for the solver-level tests.

#[test]
fn kleene_tuple_membership_local_var_all_proved() {
    let out = run_file("kleene_tuple_local_var.cantor");
    assert_eq!(
        out.code, 0,
        "kleene_tuple_local_var.cantor should exit 0\nstdout: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  counterexample  ") && !out.stdout.contains("  unknown  "),
        "expected all proved:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("cvc5") && !out.stderr.contains("cvc5"),
        "must not leak a raw cvc5 abort:\nstdout: {}\nstderr: {}",
        out.stdout,
        out.stderr
    );
}
