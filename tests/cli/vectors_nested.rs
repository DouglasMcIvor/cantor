use super::helpers::*;

// ── Nested vectors (X**) ─────────────────────────────────────────────────────

#[test]
fn vectors_nested_pure_fns_proved() {
    // Pure-expression-body functions on Nat** must be fully proved by the solver.
    // (inner_len/get_elem, this fixture's block-body functions, are NOT checked
    // here — they index a fixed position into an unconstrained Nat**/Nat*
    // parameter with no minimum-length guarantee, which the solver now
    // correctly reports as a Counterexample now that `return` is checked at
    // all, rather than masking it behind a blanket Unknown. That's a genuine,
    // known gap in these fixtures' signatures, deliberately left as-is.)
    let out = run_file("vectors_nested.cantor");
    assert!(out.stdout.contains("proved          make_nested"), "make_nested not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          identity_nested"), "identity_nested not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          outer_len"),   "outer_len not proved:\n{}",  out.stdout);
}

#[test]
fn vectors_nested_run_outer_len() {
    // vectors_nested.cantor also defines concat_nested, which is Unknown
    // (early-return solver limitation, unrelated to outer_len) — the
    // ConstrainedTree gate is whole-file, so `cantor run` refuses even
    // though `main` itself never calls concat_nested.
    let out = run_subcommand("vectors_nested.cantor");
    assert_run_refused_due_to_unknown(&out);
}

#[test]
fn vectors_nested_deep_index_and_concat() {
    // concat_len (early-return) is Unknown; the whole-file ConstrainedTree
    // gate means `cantor run` now refuses regardless of get_deep's own proof.
    let out = run_subcommand("vectors_nested_index.cantor");
    assert_run_refused_due_to_unknown(&out);
}

// ── Triple-nested vectors (Nat***) ───────────────────────────────────────────

#[test]
fn vectors_triple_nested_run_deep_index() {
    // Same early-return Unknown pattern as the other vectors_* fixtures.
    let out = run_subcommand("vectors_triple_nested.cantor");
    assert_run_refused_due_to_unknown(&out);
}

// ── Struct vectors ((A * B)*) ────────────────────────────────────────────────

#[test]
fn vectors_struct_pure_fns_proved() {
    // make_pairs, pair_vec_len, first_fst, third_snd, and main are provable:
    // literal-array indexing has tuple sort in the solver (no bounds obligation),
    // so ApplySelector resolves field access statically.
    let out = run_file("vectors_struct.cantor");
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}", out.stdout
    );
    assert!(out.stdout.contains("proved          make_pairs"),   "make_pairs not proved:\n{}",   out.stdout);
    assert!(out.stdout.contains("proved          pair_vec_len"), "pair_vec_len not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          first_fst"),    "first_fst not proved:\n{}",    out.stdout);
    assert!(out.stdout.contains("proved          third_snd"),    "third_snd not proved:\n{}",    out.stdout);
}

#[test]
fn vectors_struct_run_outer_len() {
    // vectors_struct.cantor also defines concat_struct, which is Unknown
    // (early-return solver limitation) — whole-file gate refuses the run.
    let out = run_subcommand("vectors_struct.cantor");
    assert_run_refused_due_to_unknown(&out);
}

#[test]
fn vectors_struct_literal_index_proj() {
    // first_fst() = [(1,10),(2,20),(3,30)][0].0 = 1
    // All three functions are proved (literal arrays have tuple sort → statically provable).
    let out = run_subcommand("vectors_struct_fst.cantor");
    assert_eq!(out.code, 0, "run should exit 0\nstdout: {}", out.stdout);
    assert!(out.stdout.contains("main() = 1"), "expected 'main() = 1':\n{}", out.stdout);
    assert!(out.stdout.contains("proved          first_fst"), "first_fst not proved:\n{}", out.stdout);
    assert!(out.stdout.contains("proved          third_snd"), "third_snd not proved:\n{}", out.stdout);
}

#[test]
fn vectors_struct_block_index_and_concat() {
    // Same fixture/reason as vectors_struct_run_outer_len — no counterexamples,
    // but concat_struct's Unknown result still refuses the whole-file run.
    let out = run_subcommand("vectors_struct.cantor");
    assert_run_refused_due_to_unknown(&out);
    assert!(!out.stdout.contains("  counterexample  "), "unexpected counterexample:\n{}", out.stdout);
}

// ── Vectors: block-body coercion, xs[i] indexing, ++ concatenation ───────────

#[test]
fn vectors_extended_no_counterexamples() {
    // Block-body functions using `return` on `let`-bound vector locals
    // (block_coerce_len, concat_lit, bool_concat_len) are correctly Unknown —
    // the solver can't yet reason about len()/++ on an opaque runtime vector
    // binding, a separate, known gap from `return` itself.
    //
    // get_second is a genuine, expected exception: it indexes a fixed
    // position into an unconstrained `Nat*` parameter with no minimum-length
    // guarantee, which the solver now correctly reports as a Counterexample
    // now that `return` is checked at all (previously masked behind the
    // blanket "early return unsupported" Unknown). This is deliberately left
    // as-is rather than tightening the fixture's signature.
    let out = run_file("vectors_extended.cantor");
    assert!(
        out.stdout.contains("counterexample  get_second"),
        "expected get_second's known counterexample:\n{}", out.stdout
    );
    let unexpected_counterexample = out.stdout.lines()
        .any(|l| l.contains("  counterexample  ") && !l.contains("get_second"));
    assert!(!unexpected_counterexample, "unexpected counterexample:\n{}", out.stdout);
}

#[test]
fn vectors_extended_concat_coerce_block_len() {
    // concat_lit uses an early `return` — Unknown (solver limitation), so
    // the whole-file ConstrainedTree gate refuses `cantor run`, even though
    // main() itself (which calls concat_lit) would compute the right answer.
    let out = run_subcommand("vectors_extended_concat.cantor");
    assert_run_refused_due_to_unknown(&out);
}

#[test]
fn vectors_extended_index_elem() {
    // get_elem indexes a fixed position into an unconstrained `Nat*`
    // parameter with no minimum-length guarantee — a genuine, known
    // Counterexample now that `return` is checked at all (previously masked
    // behind a blanket Unknown), not a Class of bug this fix addresses.
    // `cantor run` correctly refuses even though main()/make_vec are proved.
    let out = run_subcommand("vectors_extended_index.cantor");
    assert_run_refused(&out);
    assert!(
        out.stdout.contains("counterexample  get_elem"),
        "expected get_elem's known counterexample:\n{}", out.stdout
    );
}

#[test]
fn vectors_extended_bool_concat_len() {
    // bool_concat_len uses an early `return` — Unknown (solver limitation),
    // so `cantor run` refuses even though main() would compute the right answer.
    let out = run_subcommand("vectors_extended_bool_concat.cantor");
    assert_run_refused_due_to_unknown(&out);
}
