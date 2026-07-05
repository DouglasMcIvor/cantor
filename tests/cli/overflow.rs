//! int-soundness-plan phase 1 — checked arithmetic, end to end — and phase 3
//! step 4b, which supersedes phase 1's *abort* behaviour specifically for
//! unbounded `Kind::Int` positions: an overflowing operation now promotes to
//! a boxed `BigInt` and keeps computing the exact correct result instead of
//! aborting. Phase 1's abort path is still real code (see `compile_arith`'s
//! `Kind::Int64` branch) but is only ever reached by a raw `Int64` position —
//! and every raw `Int64` position today comes from Step A promotion or a
//! step 4a split, both of which only fire once the solver has *proved* the
//! body can't overflow in the first place. So there's no longer a realistic
//! (non-compiler-bug) program that hits the abort branch — these tests now
//! assert the promotion behaviour instead.
//!
//! Counterexample/unknown overflow obligations must never be a compile-time
//! refusal (see soundness_diagnostics.rs's `assert_run_refused` for what a
//! *real* refusal looks like — these tests assert the opposite: the file
//! still reports fully `proved` and `cantor run` still executes).

use super::helpers::*;

#[test]
fn unbounded_mul_promotes_to_bigint_instead_of_aborting() {
    // 4611686018427387904 * 2 = 9223372036854775808 = i64::MAX + 1 — exceeds
    // i64, so this used to abort (phase 1); now it promotes and computes the
    // exact correct (if now BigInt-backed) result.
    let out = run_subcommand("overflow_mul.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0 (promotes instead of aborting):\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 9223372036854775808"),
        "expected the exact correct product:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains("proved          mul"),
        "the range claim itself (Int*Int -> Int) is still proved:\n{}",
        out.stdout
    );
}

#[test]
fn unbounded_mul_runs_normally_when_no_overflow_occurs() {
    let out = run_subcommand("overflow_mul_ok.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 42"),
        "expected correct result:\n{}",
        out.stdout
    );
}

#[test]
fn unbounded_add_promotes_at_i64_max() {
    // i64::MAX + 1 = 9223372036854775808 — used to abort, now promotes.
    let out = run_subcommand("overflow_add.cantor");
    assert_eq!(out.code, 0, "expected exit 0:\n{}", out.stdout);
    assert!(
        out.stdout.contains("main() = 9223372036854775808"),
        "stdout: {}",
        out.stdout
    );
}

#[test]
fn unbounded_sub_promotes() {
    // -9223372036854775807 - 2 = -9223372036854775809 — one past i64::MIN.
    let out = run_subcommand("overflow_sub.cantor");
    assert_eq!(out.code, 0, "expected exit 0:\n{}", out.stdout);
    assert!(
        out.stdout.contains("main() = -9223372036854775809"),
        "stdout: {}",
        out.stdout
    );
}

#[test]
fn negating_i64_min_promotes() {
    // -i64::MIN = 9223372036854775808 — one past i64::MAX, the classic
    // negation-overflow case.
    let out = run_subcommand("overflow_neg.cantor");
    assert_eq!(out.code, 0, "expected exit 0:\n{}", out.stdout);
    assert!(
        out.stdout.contains("main() = 9223372036854775808"),
        "stdout: {}",
        out.stdout
    );
}

#[test]
fn division_of_i64_min_by_neg_one_promotes() {
    // The one case division can overflow: divisor-nonzero (a separate, hard
    // proof gate) is satisfied here, but plain i64::MIN/-1 is UB in LLVM's
    // sdiv — this used to abort, now `cantor_bigint_div` computes the exact
    // (BigInt-backed) answer, 9223372036854775808.
    let out = run_subcommand("overflow_div_min_neg1.cantor");
    assert_eq!(out.code, 0, "expected exit 0:\n{}", out.stdout);
    assert!(
        out.stdout.contains("main() = 9223372036854775808"),
        "stdout: {}",
        out.stdout
    );
}

#[test]
fn ordinary_division_unaffected_by_overflow_channel() {
    // Regression: the new MIN/-1 guard must not interfere with normal
    // division, nor with the existing divisor-nonzero obligation.
    let out = run_subcommand("overflow_div_ok.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 3"),
        "expected correct result:\n{}",
        out.stdout
    );
}

#[test]
fn bounded_multiply_at_extreme_values_runs_correctly() {
    // Int32*Int32 -> Int: the solver should prove no i64 overflow is
    // possible, eliding the check — this asserts the elided path still
    // computes the right answer (the elision decision itself is asserted
    // directly against `ConstrainedTree::overflow_checks` in
    // tests/solver/overflow.rs; `llvm-ir` can't help here since that
    // subcommand deliberately skips the solver and would show a checked
    // instruction either way).
    let out = run_subcommand("overflow_bounded_mul.cantor");
    assert_eq!(
        out.code, 0,
        "expected exit 0:\nstdout: {}\nstderr: {}",
        out.stdout, out.stderr
    );
    assert!(
        out.stdout.contains("main() = 4611686014132420609"),
        "expected 2147483647*2147483647:\n{}",
        out.stdout
    );
}

// ── Known issues (found in review, 2026-07-05) ──────────────────────────────
//
// int-soundness-plan.md's phase 3 writeup already flags one instance of this
// as a "known issue": bounding `int64_split`'s own `Int64 -> Int64` trial to
// self-multiplication (`x * x`, as opposed to `x * y`) made cvc5 hang past a
// 2000ms `tlimit`, confirmed past 90+ seconds of wall-clock time -- mitigated
// there only by having `try_split` skip any candidate whose body contains a
// `Mul` at all (`body_contains_mul`).
//
// That framing undersells the scope. This review reproduced the hang with
// *no* `int64_split` involvement whatsoever -- plain, ordinary phase-1
// overflow-obligation checking (predates phase 3 entirely) on the most
// natural nonlinear expression a user could write:
//
//   f : Int32 -> Int32   -- also reproduces with Int64, and with the bare
//   f(x) = x * x         -- unbounded Int builtin -- domain size isn't it.
//
// Confirmed (outside the test suite, since this hangs indefinitely):
// `cantor --timeout 2 run` on the Int32 case above still hadn't returned
// after 20 real seconds -- cvc5 does not honor `tlimit` for this query shape
// at all, so the CLI's own documented escape hatch doesn't help a user who
// hits this. `Int16 -> Int16` (a smaller bound) returns a real counterexample
// in ~2.7s; `Int8 -> Int8` in ~0.05s -- so it's specifically the *bound's
// magnitude*, not the self-multiplication pattern alone, that pushes cvc5
// into this non-terminating (or at least extremely slow, past 90s) state.
// Given the CLI has no working timeout for this, and `int64_split`'s
// mitigation only covers its own internal trial, this is a live, easily-hit
// hang in the shipped compiler for any function whose body squares one of
// its own bounded (Int32/Int64-ish) parameters -- not just a narrow
// compiler-internal corner case.
//
// These use `run_subcommand_with_deadline` (not the plain `run_subcommand`
// every other test in this file uses) specifically so that if/when this is
// fixed, removing `#[ignore]` makes the test assert real, fast, correct
// behaviour rather than merely "didn't hang" -- and so that running these
// under `cargo test -- --ignored` before a fix lands fails cleanly instead of
// wedging the test binary.
mod known_issues {
    use std::time::Duration;

    use super::*;

    #[test]
    #[ignore = "cvc5 hangs (confirmed past 90+ seconds, --timeout has no \
                effect) on a bounded self-multiplication existential -- see \
                this module's doc comment. f : Int32 -> Int32; f(x) = x * x \
                should report a counterexample (x = 46341 squares to \
                2147488281, outside Int32) in well under a second, the way \
                the analogous Int16 case already does."]
    fn bounded_self_multiplication_does_not_hang_cvc5() {
        let out = run_subcommand_with_deadline("self_mult_int32.cantor", Duration::from_secs(10))
            .expect(
                "cantor run should not hang indefinitely on `f : Int32 -> Int32; f(x) = x * x`",
            );
        assert_ne!(
            out.code, 0,
            "expected a refused run (counterexample: 46341*46341 overflows Int32):\n{}\n{}",
            out.stdout, out.stderr
        );
        assert!(
            out.stdout.contains("counterexample"),
            "expected a reported counterexample:\n{}",
            out.stdout
        );
    }

    #[test]
    #[ignore = "the original int-soundness-plan.md repro, verbatim: cvc5 \
                hangs on f : Int -> Int; f(x) = x * x even though the domain \
                is the bare, fully-unconstrained Int builtin -- see this \
                module's doc comment for why this rules out \"it's about the \
                huge bounded existential specifically\" as the root cause."]
    fn unconstrained_self_multiplication_does_not_hang_cvc5() {
        let out =
            run_subcommand_with_deadline("self_mult_unconstrained.cantor", Duration::from_secs(10))
                .expect(
                    "cantor run should not hang indefinitely on `f : Int -> Int; f(x) = x * x`",
                );
        assert_eq!(
            out.code, 0,
            "expected exit 0 (proved, x*x can overflow but that's an \
             overflow-channel matter, not a range-contract counterexample):\n{}\n{}",
            out.stdout, out.stderr
        );
    }
}
