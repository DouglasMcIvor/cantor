# Closing the i64 soundness gap: plan

**Status:** phase 1 DONE (2026-07-04) — see `docs/design-decisions.md`'s
"Checked arithmetic" entry for the decided semantics table. Phase 2 DONE
(2026-07-04) — see `docs/design-decisions.md` §7 for the decided details
(arity as a free dispatch key, disjointness/Kind-agreement scoped to a
(name, arity) group). Phase 3 not started.
**Executes in three phases; phase 1 alone closes the soundness gap**

---

## The gap

The solver reasons in unbounded ℤ; codegen stores every integer in an i64 and
emits plain `add`/`sub`/`mul` instructions. `f : Int * Int -> Int` with
`f(x, y) = x * y` is proved mathematically, yet the JIT wraps silently past
±2⁶³ — a proved theorem is visibly false at runtime. This is the one place the
compiler currently violates its own core principle ("never silently assume
anything that isn't proved"): every unchecked arithmetic instruction silently
assumes its result fits in a machine word.

Two distinct problems hide inside this gap, and they have different fixes:

- **Soundness** — a proved claim can be *false* at runtime (wrong answers).
- **Completeness** — the runtime can't *represent* all of ℤ (some valid
  programs can't run to completion).

Phase 1 (checked arithmetic) closes soundness cheaply and immediately.
Phases 2–3 (function overloading, then BigInt — the backlog's agreed order)
close completeness. Nothing in phase 1 is throwaway: the proved-→-elide
machinery decides which operations BigInt can leave on the raw fast path, and
the overflow-trap branch is exactly where BigInt promotion will later slot in.

---

## Phase 1 — Checked arithmetic (closes soundness)

### Semantics

Every arithmetic operation on integers (`Add`, `Sub`, `Mul`, `Div`,
`UnOp::Neg`) carries an implicit compiler-generated claim:

> the operation's result, computed in ℤ, lies in `Int64`

checked by the solver under the function's domain constraints, with the
`assert` gradient applied — but with one deliberate difference at the bottom
rung:

| Solver outcome | Codegen |
|---|---|
| proved | plain instruction, exactly as today — zero cost |
| unknown | checked instruction + abort branch |
| counterexample | checked instruction + abort branch (**not** a compile error) |

Counterexample must **not** be an error: `f(x, y) = x * y : Int * Int -> Int`
is a theorem in ℤ and stays a valid Cantor program. Overflow is a
*representation* limitation of the current runtime, not a domain violation by
the developer. Contrast the existing divisor obligation (`encode.rs`
`builtin_arg_constraints`): dividing by zero is meaningless in ℤ itself, so it
stays a hard counterexample-error. Overflow is different in kind and gets the
soft treatment.

Aborting is consistent with the design principles: the compiler still assumes
nothing unproved — it *checks* the unproved fact at runtime and refuses to
continue with a wrong value. Wrap-around was the silent assumption; the abort
is the honest fallback, in the same family as stack exhaustion or OOM (which
even a full BigInt runtime can hit). Once phase 3 lands, the abort branch
becomes the BigInt promotion branch and the completeness caveat disappears.

### What to check, exactly

- `Add`, `Sub`, `Mul`: LLVM `llvm.sadd.with.overflow.i64` /
  `ssub` / `smul` intrinsics; branch to abort on the overflow flag.
- `UnOp::Neg`: overflows only at `i64::MIN` — either `ssub.with.overflow(0, x)`
  or an explicit compare.
- `Div`: divisor-nonzero is already a hard obligation; the remaining case is
  `i64::MIN / -1` (UB in LLVM `sdiv`). Emit an explicit guard when the claim
  `result ∈ Int64` isn't proved.
- Out of scope for phase 1 (note, don't fix): integer literals larger than
  i64 are already rejected by the lexer (`InvalidIntLiteral`) — under ℤ
  semantics that rejection is really `Unsupported`, revisit in phase 3;
  vector lengths / concat sizes / loop counters are internal i64 quantities
  not exposed to user arithmetic.

### Solver side

- The claim is an ordinary range check on the operation's SMT term against the
  existing `Int64` builtin bounds (`builtins.rs` already defines them) under
  the current path constraints — same machinery as domain/range checks and the
  divisor obligation. No new encoding concepts.
- Record the outcome per arithmetic node on the `ConstrainedTree` (e.g. a
  `needs_overflow_check: bool` on the node), following the existing pattern of
  codegen being gated by solver-recorded proofs.
- Expect `Mul` goals under unconstrained domains to come back unknown
  (nonlinear arithmetic) — that's correct and honest; the check gets emitted.
  Code operating on `Int8`–`Int32`-bounded domains should prove easily and
  stay on the raw path.

### Codegen / runtime side

- `compile_arith` (`codegen/expr.rs`) consults the node flag: plain build
  when proved, `*.with.overflow` + conditional branch to an abort block
  otherwise.
- Abort path: new runtime function `cantor_overflow_abort(msg)` (declared in
  `runtime_decls.rs`, implemented in `runtime/mod.rs`) that prints the message
  — including the source span, baked in as a constant string at compile time —
  and exits nonzero. It does **not** route through the `Fail` wire: that would
  force `| Fail` onto every range containing arithmetic, changing the meaning
  of existing programs.

### Tests and docs

- CLI end-to-end: an unbounded `Int * Int -> Int` multiply fed boundary values
  aborts with the overflow message (not a wrong value); a bounded-domain
  program (`Int32 * Int32 -> Int`) at its extreme values runs correctly with
  no abort; solver tests that the proved case elides (assert on the recorded
  flag or on emitted IR).
- README: replace the "Known unsoundness (v0)" call-out with a "Known
  incompleteness" one — proved claims can no longer be false at runtime, but
  values escaping i64 abort until BigInt lands.
- design-decisions.md: add the overflow policy (this section's semantics
  table) as a decided item.

---

## Phase 2 — Function overloading with multiple bodies

**DONE (2026-07-04).** Implemented in the 5-step order below, each its own
commit. One design point came up during implementation and was resolved with
Doug rather than assumed: **arity is a free dispatch key** — overloads of one
name may have different parameter counts (not just different domains at one
arity), since a call's argument count is always known at parse time and
needs no solver call to resolve. Kind-agreement and the disjointness
obligation are scoped to a (name, arity) group accordingly; see
design-decisions.md §7 for the decided details. Also fixed a latent
`main.rs` reporting bug along the way (`item_by_name` collapsed same-named
items via a last-wins `HashMap` and indexed `def.sigs[i]` against whichever
one survived — harmless before phase 2 since no name ever repeated, but
would have panicked or mis-displayed as soon as overload sets, or the new
disjointness-check result entries, existed).

The design is already **DECIDED** in design-decisions.md §7; this phase
implements it. Today "overloading" means multiple signatures sharing one body;
this adds multiple `FunctionDef`s sharing one name, each with its own body.
The settled rules:

- Overload domains must be **provably disjoint**; overlap is a compile error.
- Call-site resolution is a proof obligation: static-proof-first, runtime
  membership-test fallback — the same pattern as everywhere else.
- Automatic domain-partition inference stays deferred (phase 3 adds one
  compiler-generated split as a special case, not the general feature).

Suggested step order (parser → semantics → solver → codegen, per CLAUDE.md):

1. **Parser / grouping** — allow repeated `FunctionDef`s with the same name.
   Verify what happens today (likely silent shadowing in a map — if so, that's
   a latent bug worth a test) and make grouping into an overload set explicit
   in the semantic phase.
2. **Semantics** — an overload set is a `Vec` of definitions under one name.
   Keep the existing rule that all signatures across the set agree on the
   `Kind` of each position (elaborate.rs); relaxing per-overload `Kind`s is
   deliberately deferred to phase 3 and should fail loudly if hit before then.
3. **Solver** —
   - each body is verified against its own signatures only (reuses the
     existing multi-signature checking, applied per definition);
   - new pairwise **disjointness obligations** between overload domains — a
     counterexample is a witness value in both domains, reported with both
     definitions' spans;
   - call sites already require the argument to lie in the union of declared
     domains — that carries over unchanged;
   - static resolution: try to prove the argument lies in one specific
     overload's domain; record the resolution (or its absence) on the
     `ConstrainedTree` call node. Per-signature `?`-narrowing and range
     narrowing then apply per resolved overload, as they do today per
     signature.
4. **Codegen** — one LLVM function per overload (mangled by index). Statically
   resolved calls compile to a direct call. Unresolved calls compile to a
   membership-test dispatch chain (`membership.rs` machinery) — order
   irrelevant since domains are disjoint, and the final else-arm is
   unreachable because the solver proved union coverage; still emit a loud
   trap there per the fail-loudly principle.
5. **Tests / docs** — CLI e2e: static dispatch, runtime dispatch, overlap
   rejection with witness, recursion where one overload calls another.
   README: move overloading from roadmap to features; design-decisions §7
   status update.

Phase 2 does not itself touch the soundness gap, but it builds the exact
machinery phase 3's `Int64`/BigInt split rides on: several compiled bodies
per name, proof-gated static dispatch, membership-test runtime dispatch.

---

## Phase 3 — BigInt runtime (closes completeness)

This phase needs its own detailed design doc once phases 1–2 land; the sketch
below records the intended shape and the open decisions, not a work plan.

- **Runtime library:** `num-bigint` (mature, pure Rust).
- **Representation (OPEN — recommendation below):** positions the compiler
  can bound within `Int64` keep today's raw i64. Positions of unbounded `Int`
  / `Nat` become a **one-word tagged value**: low bit 0 → small integer in
  the upper 63 bits; low bit 1 → pointer to a heap BigInt. Keeping every slot
  physically i64 means Arrow `Int64Array` vectors, struct layouts, the `Fail`
  wire and `cantor_main_into` stay physically unchanged — only the
  *interpretation* of unbounded positions changes. The alternative (an
  `{i1, i64}` struct like the `Fail` wire) is simpler to reason about but
  changes every layout that embeds an `Int`.
- **Phase 1's abort branch becomes the promotion branch:** checked op
  overflows → box into a BigInt and continue on the tagged path, instead of
  aborting.
- **The backlog's overload split:** `foo : Int -> Int` compiles to an `Int64`
  overload (raw calling convention) and a `BigInt = Int - Int64` overload,
  using phase 2's dispatch machinery. A program whose call sites all prove
  `Int64` membership never references a bigint symbol, so the library isn't
  linked — the backlog's goal. This requires relaxing phase 2's
  same-`Kind`-per-position rule for compiler-generated splits.
- **Known hard part (flagging now, solving later):** inside the `Int64`
  overload's body, an intermediate result that isn't proved bounded can still
  overflow, and its consumers must then handle a tagged value — so raw vs
  tagged is a per-position property derived from solver-proved bounds, not a
  per-function property. The overload split buys monomorphic *calling
  conventions*; it does not eliminate tagged locals inside bodies.
- `require x not in BigInt` / `assert x not in BigInt` (backlog) fall out of
  `BigInt` being an ordinary named set once the split exists.

---

## Order of execution and why

1. **Phase 1 first** — small (solver obligation machinery and the
   proof-gated-codegen pattern both already exist), immediately converts
   "silently wrong" into "loudly aborts", and directly feeds phase 3.
2. **Phase 2 second** — a roadmap feature in its own right, fully designed,
   no dependency on phase 1.
3. **Phase 3 last** — depends on both; gets its own design doc first.

## Open questions (for Doug)

1. ~~Phase 1 abort semantics~~ **DECIDED**: process abort with a
   `path:line:col`-prefixed message, implemented as `cantor_overflow_abort`.
2. Phase 3 representation: tagged word vs `{i1, i64}` struct — deferred to
   the phase 3 design doc, no need to decide now.
3. Should phase 1's emitted checks be surfaceable (e.g. a `--list-overflow-checks`
   flag) so a developer can hunt down and prove away hot-path checks?
   Nice-to-have, not in scope unless cheap — still open; not implemented.
