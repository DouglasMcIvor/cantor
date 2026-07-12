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
    assert!(
        out.stdout.contains("proved          make_nested"),
        "make_nested not proved:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          identity_nested"),
        "identity_nested not proved:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          outer_len"),
        "outer_len not proved:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_nested_run_outer_len() {
    // `Nat**` local-vector-let bindings (block_nested, concat_nested) are now
    // real-sequence-encoded and correctly proved (previously opaque-integer
    // Unknown). The whole-file gate still refuses `cantor run` here, but now
    // for a different, pre-existing, unrelated reason: inner_len/get_elem
    // index a fixed position into an unconstrained `Nat**`/`Nat*` parameter
    // with no minimum-length guarantee, a genuine known gap in these
    // fixtures' signatures (see `vectors_nested_pure_fns_proved`), which the
    // solver correctly reports as a Counterexample, not Unknown.
    let out = run_subcommand("vectors_nested.cantor");
    assert_run_refused(&out);
    assert!(
        !out.stdout.contains("  unknown  "),
        "expected no `unknown` line (only the known inner_len/get_elem \
         counterexamples):\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  inner_len"),
        "expected inner_len's known counterexample:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  get_elem"),
        "expected get_elem's known counterexample:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_nested_deep_index_and_concat() {
    // `Nat**` local-vector-let bindings are now real-sequence-encoded: both
    // get_deep (nested `xss[i][j]` indexing) and concat_len (`++`) are
    // proved, and `cantor run` actually executes main() = get_deep() = 50
    // (xss[1][2] on [[10,20],[30,40,50]]) — previously Unknown/refused.
    let out = run_subcommand("vectors_nested_index.cantor");
    assert_eq!(
        out.code, 0,
        "run should exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 50"),
        "expected 'main() = 50':\n{}",
        out.stdout
    );
}

// ── Triple-nested vectors (Nat***) ───────────────────────────────────────────

#[test]
fn vectors_triple_nested_run_deep_index() {
    // `Nat***` local-vector-let bindings are now real-sequence-encoded and
    // correctly proved (get_deep, concat_triple). The whole-file gate still
    // refuses `cantor run`, but now for a different, pre-existing, unrelated
    // reason: middle_len indexes a fixed position into an unconstrained
    // `Nat***` parameter with no minimum-length guarantee (same known gap as
    // vectors_nested.cantor's inner_len/get_elem).
    let out = run_subcommand("vectors_triple_nested.cantor");
    assert_run_refused(&out);
    assert!(
        !out.stdout.contains("  unknown  "),
        "expected no `unknown` line (only the known middle_len \
         counterexample):\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("counterexample  middle_len"),
        "expected middle_len's known counterexample:\n{}",
        out.stdout
    );
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
        "unexpected counterexample:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          make_pairs"),
        "make_pairs not proved:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          pair_vec_len"),
        "pair_vec_len not proved:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          first_fst"),
        "first_fst not proved:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          third_snd"),
        "third_snd not proved:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_struct_run_outer_len() {
    // `(Nat * Nat)*` local-vector-let bindings (block_struct_len,
    // block_struct_index, concat_struct) are now real-sequence-encoded and
    // correctly proved (previously opaque-integer Unknown) — `cantor run`
    // now actually executes main() = pair_vec_len(make_pairs()) = 3.
    let out = run_subcommand("vectors_struct.cantor");
    assert_eq!(
        out.code, 0,
        "run should exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3"),
        "expected 'main() = 3':\n{}",
        out.stdout
    );
}

#[test]
fn vectors_struct_literal_index_proj() {
    // first_fst() = [(1,10),(2,20),(3,30)][0].0 = 1
    // All three functions are proved (literal arrays have tuple sort → statically provable).
    let out = run_subcommand("vectors_struct_fst.cantor");
    assert_eq!(out.code, 0, "run should exit 0\nstdout: {}", out.stdout);
    assert!(
        out.stdout.contains("main() = 1"),
        "expected 'main() = 1':\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          first_fst"),
        "first_fst not proved:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          third_snd"),
        "third_snd not proved:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_struct_block_index_and_concat() {
    // Same fixture as vectors_struct_run_outer_len — everything proves and
    // runs cleanly now, no counterexamples and no unknowns.
    let out = run_subcommand("vectors_struct.cantor");
    assert_eq!(
        out.code, 0,
        "run should exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        !out.stdout.contains("  counterexample  "),
        "unexpected counterexample:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("  unknown  "),
        "unexpected unknown:\n{}",
        out.stdout
    );
}

// ── Vectors: block-body coercion, xs[i] indexing, ++ concatenation ───────────

#[test]
fn vectors_extended_no_counterexamples() {
    // Block-body functions using `return` on `let`-bound vector locals
    // (block_coerce_len, concat_lit, bool_concat_len) are now real-sequence-
    // encoded and correctly proved (previously opaque-integer Unknown).
    //
    // get_second is a genuine, expected exception: it indexes a fixed
    // position into an unconstrained `Nat*` parameter with no minimum-length
    // guarantee, which the solver correctly reports as a Counterexample —
    // deliberately left as-is rather than tightening the fixture's signature.
    let out = run_file("vectors_extended.cantor");
    assert!(
        out.stdout.contains("counterexample  get_second"),
        "expected get_second's known counterexample:\n{}",
        out.stdout
    );
    let unexpected_counterexample = out
        .stdout
        .lines()
        .any(|l| l.contains("  counterexample  ") && !l.contains("get_second"));
    assert!(
        !unexpected_counterexample,
        "unexpected counterexample:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_extended_concat_coerce_block_len() {
    // concat_lit's local `Nat*` `let`s (xs, ys, zs) are now real-sequence-
    // encoded and correctly proved — `cantor run` executes main() =
    // concat_lit() = len([1,2] ++ [3,4]) = 4.
    let out = run_subcommand("vectors_extended_concat.cantor");
    assert_eq!(
        out.code, 0,
        "run should exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 4"),
        "expected 'main() = 4':\n{}",
        out.stdout
    );
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
        "expected get_elem's known counterexample:\n{}",
        out.stdout
    );
}

#[test]
fn vectors_extended_bool_concat_len() {
    // bool_concat_len's local `Bool*` `let`s are now real-sequence-encoded
    // and correctly proved — `cantor run` executes main() = bool_concat_len()
    // = len([true,false] ++ [false,true,true]) = 5.
    let out = run_subcommand("vectors_extended_bool_concat.cantor");
    assert_eq!(
        out.code, 0,
        "run should exit 0\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 5"),
        "expected 'main() = 5':\n{}",
        out.stdout
    );
}
