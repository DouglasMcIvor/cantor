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

// ── Self-multiplication (nl-cov fix, review 2026-07-05) ─────────────────────
//
// int-soundness-plan.md's phase 3 writeup already flagged one instance of
// this as a "known issue": bounding `int64_split`'s own `Int64 -> Int64`
// trial to self-multiplication (`x * x`, as opposed to `x * y`) made cvc5
// hang past a 2000ms `tlimit`, confirmed past 90+ seconds of wall-clock time
// -- mitigated there only by having `try_split` skip any candidate whose
// body contains a `Mul` at all (`body_contains_mul`).
//
// A later review found that framing undersold the scope: the hang reproduced
// with *no* `int64_split` involvement whatsoever -- plain, ordinary phase-1
// overflow-obligation checking (predates phase 3 entirely) on the most
// natural nonlinear expression a user could write (`f : Int32 -> Int32; f(x)
// = x * x`), and cvc5 did not honor `tlimit` for this query shape at all.
// Root cause: cvc5's default heuristic nonlinear-arithmetic engine doesn't
// terminate quickly on `x ∈ [lo, hi] ∧ (x*x < lo ∨ x*x > hi)` once the bound
// reaches Int32/Int64 size. Fixed by switching every solver construction
// site to the `nl-cov` (libpoly covering/CAD) nonlinear procedure instead --
// see docs/design-decisions.md for the rationale distinguishing this from
// the pre-existing `mbqi` option.
//
// These use `run_subcommand_with_deadline` (not the plain `run_subcommand`
// every other test in this file uses) as a regression guard: if a future
// change regresses back to the slow engine, this fails clean (deadline hit)
// rather than wedging the test binary.
mod self_multiplication {
    use std::time::Duration;

    use super::*;

    #[test]
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
