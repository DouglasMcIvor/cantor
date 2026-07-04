# Closing the i64 soundness gap: plan

**Status:** phase 1 DONE (2026-07-04) — see `docs/design-decisions.md`'s
"Checked arithmetic" entry for the decided semantics table. Phase 2 DONE
(2026-07-04) — see `docs/design-decisions.md` §7 for the decided details
(arity as a free dispatch key, disjointness/Kind-agreement scoped to a
(name, arity) group). Phase 3 design DECIDED (2026-07-04) — see the
"Phase 3 — BigInt runtime" section below for the tagged-word representation,
the `Int64`/`BigInt` overload split, and the step order. Implementation
step 1 (runtime — `CantorBigInt`, tagged encode/decode, `cantor_bigint_*`)
DONE (2026-07-04). Step 2 (semantics — `Kind::Int64` variant,
`compiler_generated_split` marker, `check_overload_kind_agreement`
exception) DONE (2026-07-04) — see that step's entry below for a correction
found while implementing it (the original sketch assumed `Int64` already
had a distinct `Kind`; it didn't). Steps 3–5 (solver, codegen, tests/docs)
not started — no LLVM/codegen/JIT wiring exists yet.
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

**Status: design DECIDED (2026-07-04), implementation not started.** The two
open questions from the earlier sketch (representation; what happens inside
an `Int64`-resolved body) are resolved below. This section is detailed enough
to work from directly — no separate design doc needed — but it is still a
large phase; expect it to land as several separate commits (see step order at
the end of this section), likely across several sessions, not one.

### Representation (DECIDED): tagged word

- **Runtime library:** `num-bigint` (mature, pure Rust). New `Cargo.toml`
  dependency, `num-bigint = "0.4"` (matches the existing style of pinning by
  major version only, e.g. `cvc5 = "0.4"`).
- Positions the compiler can bound within `Int64` keep today's raw i64,
  completely unaffected by anything below — this is a `Kind`-level split
  (see "the overload split" below), not a runtime flag on individual bytes.
  Only positions whose `Kind` is the unbounded `Int` (equivalently `Nat`, its
  lower-bounded twin) become a **one-word tagged value**:
  - low bit `0` → small integer, value = `word >> 1` (arithmetic shift,
    sign-preserving). Encode: `word = n << 1` (fine for
    `n ∈ [-2^62, 2^62 - 1]`; outside that range the value must already be
    boxed — see promotion below).
  - low bit `1` → pointer to a heap-allocated `CantorBigInt`. Decode:
    `ptr = word & !1`. Encode: `word = ptr | 1`.
- **Alignment is load-bearing, not incidental.** The decode above is only
  safe if every `CantorBigInt` heap allocation is at least 2-byte aligned
  (so bit 0 is never part of a real address). Rust's allocator guarantees
  *the type's own* alignment, no more — so `CantorBigInt` must be declared
  `#[repr(align(8))]` explicitly rather than relying on it incidentally
  containing a pointer-sized field. This is a one-line annotation, not new
  machinery.
- This choice was made over the `{i1, i64}` struct alternative (mirroring
  the `Fail` wire) specifically because it continues an existing precedent
  rather than inventing a new one: an i64 slot's meaning is already
  `Kind`-dependent everywhere a Cantor vector embeds pointers today (e.g.
  `CantorListVec` elements are "an i64 pointer to an inner vector, or a
  scalar — codegen alone knows which, via `Kind`", `runtime/mod.rs`
  lines 409–432). Tagging an unbounded-`Int` slot is the same trick one
  level down. Consequence: Arrow `Int64Array`-backed vectors, `StructArray`
  fields, tuple layouts, and the `Fail` wire need **zero** layout changes —
  only the *interpretation* of unbounded-`Int` slots changes, and only
  codegen (never the Arrow/runtime layer, which already treats every slot
  as opaque i64) needs to become tag-aware. The struct alternative would
  instead force every vector/struct/tuple position holding an unbounded
  `Int` to grow an extra column, a much larger blast radius on the
  Arrow-backed vector code for no corresponding benefit here (unlike the
  `Fail` wire, which needs its flag to be independently inspectable at
  every call boundary — a tagged `Int` doesn't).
- **Memory:** a boxed `CantorBigInt` is `Box::into_raw` and never freed,
  exactly like every other heap object in `runtime/mod.rs` today (sets,
  vectors — see the file's standing TODO about an arena scoped to the
  event-handler dispatch boundary). No refcounting/GC is being introduced
  for this feature specifically; BigInt leaks the same way everything else
  currently does.

### Phase 1's abort branch becomes the promotion branch

At every arithmetic node where the solver did not prove the `Int64` bound
(phase 1's `needs_overflow_check` flag — reinterpreted here, not renamed,
since it's the same obligation with a different codegen consequence once a
tagged-`Int` position is available to promote into):

- if the position's `Kind` is a bounded `IntN` (no tagged representation
  exists): unchanged from phase 1 — checked instruction, abort branch, no
  BigInt involved. Bounded-domain overflow really is a completeness dead
  end until someone widens the declared bound; nothing to promote into.
- if the position's `Kind` is the unbounded `Int`: checked instruction, and
  the overflow branch boxes the wide result into a `CantorBigInt` and
  continues (tagged-pointer word) instead of calling
  `cantor_overflow_abort`. New runtime entry points: `cantor_bigint_from_i64`,
  `cantor_bigint_add/sub/mul/div`, `cantor_bigint_cmp`, `cantor_bigint_to_string`
  (all take/return tagged words, so codegen never has to case-split between
  "both small", "both big", "mixed" itself — each runtime function checks its
  own operands' tag bits and dispatches, matching the existing division of
  labour where Arrow/heap details stay inside `runtime/mod.rs`).
- The solver side is unaffected: it already reasons over unbounded ℤ; the
  `Int` vs `Int64` split is purely a codegen/runtime representation choice,
  not a change to what's proved.

### The overload split

`foo : Int -> Int` compiles to two `FunctionDef` bodies sharing one name,
using phase 2's overload machinery:
- an `Int64` overload — parameters and return declared `Int64`, raw i64
  calling convention, used when a call site statically proves `Int64`
  membership for every argument;
- a `BigInt = Int - Int64` overload — parameters/return use the tagged
  representation, used otherwise (static proof of non-`Int64` membership,
  or — the common case — no proof either way, resolved by phase 2's runtime
  membership-test dispatch).

A program whose call sites all prove `Int64` membership never references a
BigInt symbol, so `num-bigint` isn't linked into the final artifact — the
whole point of doing the split at the overload level rather than always
compiling one BigInt-capable body. This **requires relaxing phase 2's
same-`Kind`-per-position rule** (`check_overload_kind_agreement`,
`semantics/elaborate.rs`) specifically for compiler-generated splits: today
that function only ever sees user-written overload sets and rejects any
`Kind` mismatch unconditionally. The relaxation needs a marker distinguishing
"this pair of overloads is a compiler-generated `Int64`/`BigInt` split" from
an ordinary user-written group, so a genuine user mistake (accidentally
writing two overloads with different parameter `Kind`s) still errors exactly
as it does today.

**Why this exception stays narrow (raised and discussed 2026-07-04, decided
not to generalize yet):** it's tempting to relax `check_overload_kind_agreement`
generally, since `Kind` is supposed to be an internal representation detail
invisible to the user (see §13 "Value layers") — rejecting a user's overload
set purely because of a `Kind` mismatch is already, in a sense, a `Kind`
leak, and phase 3 doesn't create that tension, it just adds a second,
compiler-owned instance of it. But the Int64/BigInt split is only tractable
*because* there's a single canonical Kind (tagged `Int`) that every other
member of the group converts into — that's what gives an unresolved call's
runtime-dispatch merge point (the LLVM `phi` across candidate overloads) a
well-defined target representation to convert into before merging. A general
user-facing Kind-heterogeneous overload set has no such canonical Kind in
general (e.g. `Int8 -> Int8` and `Vector(Int) -> Vector(Int)` sharing a
name) — an unresolved call site would have nothing well-defined to merge
into, short of adopting the existing `Kind::TaggedUnion` sum machinery for
every heterogeneous overload group, which raises open questions of its own
(how the canonical Kind is chosen or declared, what conversions the compiler
is allowed to assume). That's a substantial standalone feature, not a
same-sized relaxation as this one. Recorded as a deferred backlog item
(design-decisions.md §12, "General Kind-polymorphic overloading") rather
than folded into phase 3 — phase 3's concrete Int64/BigInt work is the
blueprint to generalize from once it exists, not a reason to generalize
up front.

One more wrinkle the merge point must handle: converting a *bounded* `Int64`
result into the *general* tagged representation is not always a bare shift.
`Int64` is the full i64 range, but the tagged scheme's "small" immediate only
has 63 bits of magnitude (one bit spent on the tag) — so a raw `Int64` value
with `|n| > 2^62` already fits in a machine word but still needs boxing the
moment it crosses into the general `Int` Kind, even though it never
overflowed anything. This only bites within `(2^62, 2^63)` and its mirror on
the negative side (a narrow band near the extremes of `Int64`), and only at
a boundary crossing into the general Kind — a call statically resolved to
the `Int64` overload that stays within further `Int64`-only computation
never pays this cost. Worth a dedicated codegen test once implemented (an
`Int64`-resolved call whose result is exactly, say, `2^62` flowing into a
`Vector(Int)` boxes correctly rather than corrupting the tag bit).

**Known hard part, still true after the split exists:** inside the `Int64`
overload's body, an intermediate expression that isn't itself proved bounded
(e.g. `x*x` where `x : Int64` and the domain doesn't constrain it further)
still overflows i64 in the mathematical sense, and per the rule above it must
promote into a tagged/boxed value — even though the overload's *signature*
says `Int64`. So a local inside an ostensibly-`Int64` body can still be
tagged; raw-vs-tagged is a per-expression property derived from what the
solver actually proved at that node, not a per-function property implied by
the signature. The overload split buys a monomorphic **calling convention**
at the boundary; it does not eliminate tagged locals inside bodies.

### What phase 3 does *not* need to change

- The solver: already reasons over unbounded ℤ (see above).
- Arrow-backed vector/struct/tuple layouts: unaffected by construction (see
  representation section).
- The `Fail` wire: untouched — a fallible function returning `Int` wraps a
  tagged word in the existing `{i1, i64}` struct's payload field exactly as
  it wraps a plain i64 today; the tag lives *inside* the i64, invisible to
  the `Fail` wire itself.

### Step order (parser → semantics → solver → codegen, per CLAUDE.md, plus a
runtime-first step since the BigInt arithmetic itself is pure Rust and
independently unit-testable before any codegen exists)

1. **Runtime — DONE (2026-07-04).** `CantorBigInt` (wraps `num_bigint::BigInt`,
   `#[repr(align(8))]`), tagged encode/decode helpers, and
   `cantor_bigint_{from_i64,add,sub,mul,div,neg,cmp,to_string}` in
   `src/runtime/mod.rs`, unit-tested directly in `tests/runtime.rs` (no
   LLVM/CLI involvement — not yet declared in `runtime_decls.rs` or
   registered in `jit.rs`, that's step 4).
2. **Semantics — DONE (2026-07-04).** the compiler-generated-split marker and
   the `check_overload_kind_agreement` relaxation described above. No
   user-facing syntax changes; this step is invisible to existing programs
   (confirmed by a regression test — see below).

   **Correction found while implementing (the original sketch above assumed
   this without checking): `Int64` and unbounded `Int` elaborated to the
   exact same `Kind::Int` before this step** (`semantics/builtins.rs`,
   `kind.rs`) — there was no `Kind`-level mismatch for
   `check_overload_kind_agreement` to reject in the first place, so
   "relaxing" it would have been a no-op. Added `Kind::Int64` as a genuinely
   new variant (`kind.rs`) to make the split real: reserved for the phase 3
   split alone, not produced by ordinary elaboration of the `Int64` named
   set (that still yields `Kind::Int`, unaffected) — nothing produces
   `Kind::Int64` anywhere until step 4's generator exists. Every exhaustive
   match on `Kind` across solver/codegen (7 sites: `codegen/expr.rs`,
   `expr_vec.rs`, `trampoline.rs`, `wire.rs`, `mod.rs` ×2, `solver/sort.rs`,
   plus 2 in `main.rs`) now treats `Int64` identically to `Int` — same wire
   type (i64), same CVC5 sort/constructor (`ck_Int`), since the solver
   reasons over unbounded ℤ regardless of raw-vs-tagged representation. The
   `compiler_generated_split` marker (`SemFunctionDef`, `semantics/tree.rs`)
   is `false` for everything elaborated from real source; the exception in
   `check_overload_kind_agreement` requires *both* overloads in a mismatched
   pair to be marked, and only excuses the specific `Kind::Int`/`Kind::Int64`
   pairing at a position (`kinds_agree_for_split`) — an unrelated mismatch
   (say `Int` vs `Bool`) between two marked overloads still errors. Tested
   directly against hand-built `SemFunctionDef` fixtures in
   `tests/semantics/elaborate_tests.rs` (no producer exists yet to test
   through real source), covering: the exception firing, the exception
   *not* firing for a non-Int/Int64 mismatch, the exception requiring both
   sides marked, per-position mixing of the exception with ordinary exact
   agreement, and a regression guard that ordinary elaboration never sets
   the marker.
3. **Solver** — none needed for the ℤ reasoning itself; only the recorded
   per-node obligation (today `needs_overflow_check`) needs its consumer
   (codegen) taught the new promotion behaviour — the obligation itself is
   unchanged.
4. **Codegen**:
   a. emit the compiler-generated `Int64`/`BigInt` overload pair for eligible
      signatures, reusing phase 2's static/runtime dispatch codegen unchanged;
   b. tagged encode/decode at every unbounded-`Int` value's construction/
      consumption site (literals, arithmetic results, vector/struct/tuple
      element get/set, function parameters/returns, the `Fail` wire's payload
      field when its success `Kind` is unbounded `Int`);
   c. replace phase 1's abort branch with the promotion branch at unbounded-
      `Int` arithmetic nodes (bounded-`IntN` nodes keep the phase 1 abort,
      unchanged);
   d. comparisons (`<`, `<=`, `==`, …) and printing on tagged values route
      through `cantor_bigint_cmp` / `cantor_bigint_to_string` when either
      operand's tag bit indicates a boxed value — an early tag check lets
      the common both-small case stay on the raw i64 comparison instruction.
5. **Tests / docs**: CLI e2e covering (i) a call proved `Int64` compiles to
   the raw overload with no promotion codegen at all (assert on emitted IR,
   mirroring phase 1's "proved elides" test); (ii) a call that overflows i64
   promotes and continues to a correct (if now BigInt-backed) result instead
   of aborting; (iii) an unresolved call-site dispatches at runtime to
   whichever overload the argument's membership test picks; (iv)
   `require`/`assert ... not in BigInt` once `BigInt` is exposed as an
   ordinary named set (see below). README: retire the "Known incompleteness"
   call-out entirely — once phase 3 lands, no value can escape
   representation, closing the gap phase 1 left open. design-decisions.md:
   promote this section's representation choice from this doc into §7's
   Integers subsection as DECIDED (small pointer, full detail stays here).

`require x not in BigInt` / `assert x not in BigInt` (backlog) fall out of
`BigInt` being an ordinary named set once the split exists — no new syntax
or solver machinery, just `BigInt` needing a definition (`BigInt = Int -
Int64`) visible to name resolution the same way any other derived set is.

---

## Phase 4 (idea, deferred, not scoped) — wide-intermediate optimization

Raised 2026-07-04 while discussing phase 3, deliberately **not** designed in
detail now — recorded so the idea isn't lost. Motivating example:

```
mult_or_error : Int64 * Int64 -> Int64 | Fail
mult_or_error(x, y) {
  z = x * y
  assert z in Int64
  z
}
```

Here `x * y` may overflow i64, but the very next statement narrows straight
back to `Int64` (via `assert`, which per §"Narrowing back to IntN" in
design-decisions.md already runtime-checks and routes to `Fail` on failure
when unproved). Under phase 3 as designed, the overflowing multiply would
promote `z` to a heap `CantorBigInt` only for the `assert` to immediately
narrow it back down — real arbitrary-precision storage allocated and thrown
away in one statement.

The generalizable insight (sharper than just "this one example"): **a single
checked op's exact mathematical result always fits in double width** — the
product of two 64-bit signed integers always fits in 127 bits, a sum or
difference always fits in 65. So arbitrary-precision arithmetic is never
actually required to compute *one* operation correctly, no matter how it
overflows i64 — it's only needed once a value that's *already* boxed (i.e.
already the result of unbounded accumulation across multiple operations,
such as a loop with no fixed iteration bound) feeds into further arithmetic.
That suggests every unproved checked op could compute at i128 (cheap on real
hardware — a single widening multiply/add instruction) and only then decide,
from the exact i128 value: narrow back down (assert/range-check against the
i128 directly, no promotion at all) or, if it must escape into a genuinely
general `Int` position, construct a `CantorBigInt` directly from the i128
(`from_i128`, still no multi-limb arithmetic — arbitrary precision only
enters once a *second* boxed operand is later involved). This would also
subsume phase 1's existing overflow-flag check as a special case (checking
`Int64` membership on the i128 result is exactly comparing against
`i64::MIN`/`MAX`).

Deliberately left unscoped: whether this is worth its complexity relative to
the overflow-intrinsic approach already in place (both are cheap on real
hardware; the intrinsic is arguably simpler and is already implemented), and
whether/how to detect the "immediately narrowed, doesn't otherwise escape"
shape at the `ConstrainedTree` level (a real dataflow question the compiler
doesn't currently answer anywhere). Revisit once phase 3 is implemented and
its actual promotion overhead is measurable.

---

## Order of execution and why

1. **Phase 1 first** — small (solver obligation machinery and the
   proof-gated-codegen pattern both already exist), immediately converts
   "silently wrong" into "loudly aborts", and directly feeds phase 3.
2. **Phase 2 second** — a roadmap feature in its own right, fully designed,
   no dependency on phase 1.
3. **Phase 3 last** — depends on both; design is decided (see above), but
   implementation is its own multi-commit effort.

## Open questions (for Doug)

1. ~~Phase 1 abort semantics~~ **DECIDED**: process abort with a
   `path:line:col`-prefixed message, implemented as `cantor_overflow_abort`.
2. ~~Phase 3 representation: tagged word vs `{i1, i64}` struct~~ **DECIDED
   (2026-07-04)**: tagged word — see the "Phase 3 — BigInt runtime" section
   above.
3. Should phase 1's emitted checks be surfaceable (e.g. a `--list-overflow-checks`
   flag) so a developer can hunt down and prove away hot-path checks?
   Nice-to-have, not in scope unless cheap — still open; not implemented.
