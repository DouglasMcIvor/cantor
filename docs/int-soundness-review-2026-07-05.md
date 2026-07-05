# Phase 3 (BigInt) review — findings for Sonnet 5

Handover note from a review of the int-soundness-plan phase 3 implementation
(commits through `5421d8d`). Scope was: look for gaps beyond the two known
ones (Vector(Int)/Set(Int) elements out of scope; the `x * x` cvc5 hang).
Found one more of each kind — a correctness bug, and a much wider blast
radius on the already-known hang than the plan doc's writeup suggests — plus
validated a concrete fix for the hang. No production code was changed by this
review; five new tests were added, all currently failing and marked
`#[ignore]` with the root cause in the doc comment. Full suite (526 tests)
is green as of this note.

Suggested order: item 1 first (small, mechanical, already validated below,
unblocks the two `overflow.rs` tests), then item 2 (small, precise fix,
unblocks two `bigint.rs` tests), then decide separately whether item 3 is in
scope right now or stays deferred (it's a real feature, not a quick fix).

---

## 1. The cvc5 self-multiplication hang is much bigger than the plan doc says

**Where it's documented today:** `docs/int-soundness-plan.md`, step 4a's
"Known issue" paragraph. It frames this as specific to `int64_split`'s own
`Int64 -> Int64` trial check, mitigated there by `try_split` skipping any
candidate whose body contains a `Mul` (`body_contains_mul`,
`src/solver/int64_split.rs`).

**Why that framing undersells it:** the hang reproduces with zero
`int64_split` involvement, on plain pre-existing phase-1 overflow checking —
the most natural nonlinear expression a user could write:

```
f : Int32 -> Int32
f(x) = x * x
```

This hangs `cantor run` indefinitely. `cantor --timeout 2 run` on it still
hadn't returned after 20 real seconds. It's the bound's *magnitude*, not
self-multiplication alone or domain-unboundedness alone: `Int8 -> Int8`
returns a counterexample in ~0.05s, `Int16 -> Int16` in ~2.7s, `Int32`/`Int64`
and the bare unbounded `Int` all hang. Repro fixtures already added:
`tests/cantor_files/self_mult_int32.cantor` and
`self_mult_unconstrained.cantor` (the latter is the original
int-soundness-plan.md repro verbatim); tests in
`tests/cli/overflow.rs::known_issues` (currently `#[ignore]`d).

### Root cause, and the two separate bugs inside it

**(a) The real bug — cvc5's default nonlinear-arithmetic engine.** Confirmed
directly against the `cvc5` crate (bypassing the whole compiler for fast
iteration — see the reproduction script below) that cvc5's default nonlinear
integer arithmetic procedure does not terminate quickly on
`x ∈ [lo, hi] ∧ (x*x < lo ∨ x*x > hi)` once `lo..hi` gets to Int32/Int64
size, **even with `tlimit` set directly on that solver instance** — so this
is a genuine cvc5 behavior for this query shape, not merely a forwarding bug.

**(b) A real forwarding bug, found while chasing (a) — independent of it.**
`check_require` (`src/solver/blocks.rs`) and the loop-invariant checker
(`check_loop_inductive_step`, `src/solver/loops.rs`) — which is exactly where
the overflow obligation actually gets decided — construct a brand-new
`Solver::new(tm)` that never receives `tlimit` (or `mbqi`) at all, unlike
`configured_solver`/`check_name_def` in `src/solver/mod.rs`. So today,
`--timeout` silently does nothing for overflow/loop-invariant/require checks
regardless of question (a). Worth fixing regardless of what else lands here,
as a belt-and-suspenders: thread `timeout_ms` into both constructors the way
`configured_solver` already does.

**Important negative result — don't reach for MBQI.** `mbqi` (already
enabled globally, for sequence membership's `∀i. guard → elem∈X`
constraints) is irrelevant to this hang: the overflow obligation has no
quantifier in it at all — it's a plain existential-by-negation satisfiability
query, decided by cvc5's separate nonlinear arithmetic (NIA) module. Applying
the sequence-quantifier fix here would be treating the wrong subsystem.

### The fix: `nl-cov`, validated end to end

cvc5 has (at least) two nonlinear-arithmetic decision procedures selectable
by option: the default heuristic-based "extended nonlinear" engine, and
`nl-cov` — the newer libpoly-based covering/CAD procedure. Standalone probe
(via the `cvc5` crate directly, not through the compiler):

```rust
// examples/cvc5_probe.rs (deleted after use — not part of this handover,
// recreate from this snippet if you want to re-verify or extend it)
use cvc5::{Kind, Solver, TermManager};

fn try_self_mult(name: &str, opts: &[(&str, &str)], lo: i64, hi: i64) {
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    for (k, v) in opts {
        solver.set_option(k, v);
    }
    let x = tm.mk_const(tm.integer_sort(), "x");
    solver.assert_formula(tm.mk_term(Kind::Geq, &[x.clone(), tm.mk_integer(lo)]));
    solver.assert_formula(tm.mk_term(Kind::Leq, &[x.clone(), tm.mk_integer(hi)]));
    let xx = tm.mk_term(Kind::Mult, &[x.clone(), x.clone()]);
    let out_of_range = tm.mk_term(Kind::Or, &[
        tm.mk_term(Kind::Lt, &[xx.clone(), tm.mk_integer(lo)]),
        tm.mk_term(Kind::Gt, &[xx.clone(), tm.mk_integer(hi)]),
    ]);
    solver.assert_formula(out_of_range);
    let result = solver.check_sat(); // time it yourself if re-verifying
    println!("{name}: {:?}", result);
}
```

Results (cvc5 1.3.1, the version installed on this machine — see
`Cargo.toml`'s `cvc5 = "0.4"` pin):

| domain | default engine | `nl-cov` |
|---|---|---|
| Int8 self-bound | 14ms (sat) | 4ms (sat) |
| Int16 self-bound | 2.5s (sat) | 1.7ms (sat) |
| Int32 self-bound | **hangs past 30s**, tlimit=5000 ignored | 1.7ms (sat) |
| Int64 self-bound / unbounded | **hangs past 90s** | 1.7ms (sat) |
| Int8/Int32 domain vs. Int64 bound (should prove, i.e. unsat) | fast, correct | 1.9ms (unsat, still correct) |
| Int16 domain vs. Int64 bound (should prove) | fast, correct | 2ms (unsat, still correct) |

`nl-cov` resolved every case tried, in 1-5ms, with the correct verdict in
both directions (`sat` where a counterexample genuinely exists, `unsat`
where the claim genuinely holds) — no regressions on the "should still
prove" cases, which matters since those are exactly the common case
(`Int8`/`Int16`/`Int32`-bounded arithmetic that should stay on the free,
zero-cost proved path).

**I went further than the isolated probe:** temporarily added
`solver.set_option("nl-cov", "true");` at all five solver-construction sites
below, ran the full existing suite (526 tests) — zero failures, no
measurable slowdown — and reran the two new hang-repro tests, which now pass
in 0.04s combined (down from "never returns"). This was reverted from the
working tree before this note (per Doug: implementation is your call, not
mine), but it's fully validated; the diff is exactly this one-liner
repeated five times:

```rust
solver.set_option("nl-cov", "true");
```

at:
- `src/solver/mod.rs` — `configured_solver` (used by the two main
  signature/range checkers)
- `src/solver/mod.rs` — `check_name_def` (top-level `name : Set = value`
  constants)
- `src/solver/blocks.rs` — `check_require` (this is the one that actually
  decides the overflow obligation — see item (b) above, thread `timeout_ms`
  in here too while you're at it)
- `src/solver/loops.rs` — `check_loop_inductive_step` (same fix as above,
  same reasoning — this is the loop-invariant analogue of `check_require`)
- `src/solver/disjointness.rs` — `validate_disjoint_unions` (already takes
  `timeout_ms`, just needs the `nl-cov` option added alongside the existing
  `tlimit` line)

### Suggested commit shape

1. Add `nl-cov` at the five sites above.
2. Thread `timeout_ms` into `check_require`'s and
   `check_loop_inductive_step`'s solver construction (currently the only two
   that don't receive it at all).
3. Flip `tests/cli/overflow.rs::known_issues`'s two tests from `#[ignore]`
   to real tests (they're already written to assert the correct/fast
   behavior, not just "didn't hang" — see the module's doc comment there).
4. `docs/design-decisions.md`: a short note on why `nl-cov` is set,
   distinguishing it from the existing `mbqi` rationale (two different cvc5
   subsystems, two different bugs they each fix) — worth recording so the
   next person doesn't wonder the same thing Doug just asked about.
5. `docs/int-soundness-plan.md`: update step 4a's "Known issue" paragraph —
   it currently undersells the scope (frames this as `int64_split`-specific)
   and should note the fix + that `body_contains_mul`'s restriction in
   `try_split` can very likely be lifted once `nl-cov` is in place (re-run
   the eligibility check without the `Mul` guard and confirm before removing
   it — didn't verify this myself, but there's no obvious reason `nl-cov`
   wouldn't cover `int64_split`'s own trial the same way it covers everything
   else tried above).

---

## 2. `x in Int64` / `x in BigInt` silently return the wrong answer for ordinary small values

This is a real correctness bug (wrong boolean, not a crash), and it's in the
"BigInt as an ordinary named set" feature — the thing the plan doc marks DONE
for 2026-07-05. It's silent, so treat as higher priority than item 3 despite
being newer.

**Repro:**

```
check : Int -> Bool
check(x) = x in Int64

main : -> Bool
main() = check(100)   -- prints 0. Should be 1: 100 is trivially in Int64.
```

Complementary case (`x in BigInt`) returns the opposite wrong answer (`true`
for a small value that should be `false`). Fixtures:
`tests/cantor_files/int64_membership_small_value.cantor`,
`bigint_membership_small_value.cantor`. Tests (currently `#[ignore]`d, with
the root cause below repeated in their doc comments):
`tests/cli/bigint.rs::known_issues::int64_membership_is_true_for_an_ordinary_small_value`
and `bigint_membership_is_false_for_an_ordinary_small_value`.

**Why the two existing `BigInt`-named-set tests
(`bigint_named_set_membership_{true,false}_for_*`) didn't catch this:** both
use a bare `Int -> Int` signature for their `classify` function, which
happens to be exactly `int64_split`'s auto-split eligibility shape
(`try_split`: single param, bare `Int` domain and range, no `Mul`). Both
fixtures' `classify` gets silently rewritten into a compiler-generated
`Int64`/`BigInt` overload pair, and the call site's literal argument
statically resolves to one specific candidate — so neither test ever
actually exercises the tagged, non-split membership-check codegen path they
were meant to cover. The two new fixtures use `Int -> Bool` specifically to
dodge auto-split eligibility and force the real path.

**Root cause, precisely.** `compile_int_cmp_const`
(`src/codegen/membership.rs`, called from `compile_bounded_membership` /
`compile_outside_membership` for every `IntBound::Bounded`/`Outside` check —
`Int64`'s own bound is `Bounded(i64::MIN, i64::MAX)`, `BigInt`'s is
`Outside(i64::MIN, i64::MAX)`, `src/semantics/builtins.rs`) decides whether
to use the raw bit-pattern comparison (`small_result`) or the tag-aware
`cantor_bigint_cmp` one (`boxed_result`) by checking **only the tag bit of
`val`** (the value being tested) — it never accounts for whether the
*constant* `k` it's compared against needed boxing. `i64::MIN`/`i64::MAX`
both lie outside the tagged scheme's small-int range (`TAG_SMALL_MIN`/`MAX`,
`src/runtime/mod.rs` — one bit narrower than `Int64` itself), so `k` gets
boxed (a fresh heap pointer, via `compile_tagged_i64_const`) every single
check. For an ordinary *small*, unboxed `val`, the code picks the
raw-bit-pattern branch and ends up comparing `val`'s small shifted encoding
directly against that pointer's numeric value — not a real magnitude
comparison at all. Confirmed via runtime debug instrumentation (added
temporarily, removed): for `x = 100`, the boxed `cantor_bigint_cmp` result is
already computed and is correct, but `select`'s condition
(`is_boxed(val)`) picks the wrong (`small_result`) branch anyway.

**The fix, precisely.** `encode_small(k)` — whether the constant fits the
small-int range — is knowable at compile time (`k` is a plain `i64`, not a
runtime value), unlike `val`'s tag bit. When `encode_small(k)` is `None`
(i.e. `k` itself requires boxing), the comparison must unconditionally use
`cantor_bigint_cmp`, skipping `small_result`/`select` entirely — the
raw/select path is only ever correct when `k` is small. Concretely, in
`compile_int_cmp_const`: branch on `runtime::encode_small(k)` up front; if
`None`, emit only the `cantor_bigint_cmp`-based comparison against the
(inevitably boxed) `tagged_k`; keep today's `is_boxed(val)`-gated `select`
only for the case where `k` is small.

**Likely also affects (not separately reproduced, lower confidence):**
`int64_split`'s own runtime overload-dispatch chain
(`compile_overload_domain_match`, `src/codegen/overload_dispatch.rs`) calls
this same tag-aware membership code for the `Int64` candidate's domain
pre-check, which is exactly `Int64`'s `Bounded(i64::MIN, i64::MAX)` bound.
Not independently confirmed because `try_split` always gives both candidates
the identical body (`synth_def`), so a wrongly-chosen candidate is
unobservable at the value level unless the two candidates' raw-vs-tagged
arithmetic itself diverges (e.g. via overflow) — worth a quick check once
the fix above lands, but not blocking.

---

## 3. Vector(Int)/Set(Int) BigInt elements — already known, confirmed still fails loudly

No new finding here beyond confirming current behavior matches what's
already documented as deferred (int-soundness-plan.md step 4b's "Vector(Int)
/Set(Int)/runtime-Set for-loop storage" entry). Indexing a `Vector(Int)`
holding a boxed element aborts via `ensure_raw_int64`
(`cantor_bigint_to_i64: ... compiler invariant violated`,
`src/runtime/mod.rs`) rather than corrupting anything — consistent with
CLAUDE.md's fail-loudly principle. The message wording was already flagged
by whoever implemented step 4b as a TODO (reads like an internal-compiler-
error report for what's actually just an unimplemented feature) — not
re-litigated here.

Added one aspirational test locking in the eventual correct behavior:
`tests/cli/bigint.rs::known_issues::vector_of_int_holding_a_boxed_element_reads_back_correctly`
(`#[ignore]`d), fixture
`tests/cantor_files/vector_int_bigint_element.cantor`. This is a real
feature (arbitrary-precision container elements — canonical/deduped tagged
representation needed for `Set` equality, per the existing doc's own
reasoning), not a quick fix like items 1-2 — worth deciding separately
whether it's in scope for this pass or stays deferred.

---

## Test summary

All new, all currently `#[ignore]`d (confirmed failing via
`cargo test -- --ignored known_issues`), each with the root cause in its
doc comment:

- `tests/cli/overflow.rs::known_issues::bounded_self_multiplication_does_not_hang_cvc5`
- `tests/cli/overflow.rs::known_issues::unconstrained_self_multiplication_does_not_hang_cvc5`
- `tests/cli/bigint.rs::known_issues::int64_membership_is_true_for_an_ordinary_small_value`
- `tests/cli/bigint.rs::known_issues::bigint_membership_is_false_for_an_ordinary_small_value`
- `tests/cli/bigint.rs::known_issues::vector_of_int_holding_a_boxed_element_reads_back_correctly`

Plus a new helper, `run_subcommand_with_deadline` (`tests/cli/helpers.rs`),
for safely testing hang-prone fixtures — kills the child and returns `None`
after a deadline instead of wedging the test binary, reading stdout/stderr on
background threads so a full pipe buffer can't deadlock the wait. The two
`overflow.rs` hang tests use it in place of the ordinary `run_subcommand`;
everything else in the suite is unaffected.
