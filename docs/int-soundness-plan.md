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
had a distinct `Kind`; it didn't). Step 3 (solver) DONE (2026-07-04) —
confirmed no changes needed for the ℤ reasoning itself, plus one incidental
latent-bug fix in the phase 2 disjointness machinery found while auditing
(see that step's entry). Step 4a (the solver-gated split-generation pass)
DONE (2026-07-04) — the overload split itself was also corrected during
this step (see "The overload split" section below); a pre-existing,
unrelated cvc5 hang on self-multiplication (`x * x`) was found and logged
as a known issue rather than fixed (see step 4a's entry). Step 4b (scalar
tagged-value codegen) attempted and reverted (2026-07-04) — "scalar only,
defer call boundaries" turned out not to be a viable slice at all; see
step 4b's entry for the confirmed real scope and the (kept, inert) prep
work from the attempt: a new `cantor_bigint_to_i64` runtime function, its
`runtime_decls.rs`/`jit.rs` wiring, and an independent parameter-Kind-
binding bug fix in `codegen/mod.rs`. **Step A (whole-function `Int64`
promotion) DONE (2026-07-05)** — added *before* resuming step 4b, once
attempting it surfaced that blanket-tagging every `Kind::Int` position
would tax every integer operation in the language, not just genuinely-
unbounded ones (see "Step A — whole-function `Int64` promotion" below).
While implementing it, also found and fixed a latent gap in step 4a's own
eligibility check: it verified only the outer `domain → range` contract,
not that every arithmetic node individually stays within `Int64` — sound
for `+`/`-`/`*`/`neg`-only bodies (ring operations mod 2^64 compose safely
under a proved final-range bound) but not once a body contains `/`; both
mechanisms now share a stricter `trial_fully_proves_int64` check.

**Step 4b (tagged-value codegen) DONE (2026-07-05)**, this time landed as
one cohesive change rather than re-attempting the "scalar only, defer call
boundaries" slice that failed on 2026-07-04. Real final scope, confirmed
while implementing (each surfaced only once the previous one was fixed —
see "Step 4b — tagged-value codegen" below for the full account and the
key `tagging_active` gating decision that keeps every non-solver-verified
codegen consumer, including the entire existing test suite, on the
pre-existing plain-i64 ABI unchanged): literal/arithmetic/comparison
tagging, call-boundary encode/decode (including the function-*return*
boundary, not just call arguments — a promoted function returning another
tagged call's result needed this too), the overload-dispatch phi-merge and
per-candidate decode, `Vector(Int)`/`Set(Int)`/runtime-`Set` `for`-loop
storage (kept raw/untagged, decode-on-read/encode-on-write at that
boundary — out of scope for genuinely arbitrary-precision container
elements this pass), domain/range membership checks (`assert`/`in`,
tag-aware bound comparisons), and the `len()`/`size()`/`from()`/distinct-
constructor builtins and named-constant inlining (all of which either
returned or passed through a raw value while claiming the now-tagged
`Kind::Int` label). `expr.rs` crossed 1000 lines again during this work;
split into `codegen/arith.rs` (checked/tagged `+ - * /` and unary `-`) as
a same-session pure-refactor, mirroring the project's established pattern.
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

**Corrected 2026-07-04 (raised while starting step 4a — the original text
below the line was unsound as stated; see "Why solver-gated" below for the
counterexample and fix).** `foo : Int -> Int` *may* compile to two
`FunctionDef` bodies sharing one name, using phase 2's overload machinery —
but only when the solver additionally proves it's safe to, not
unconditionally for every unbounded-`Int` signature:
- an `Int64` overload — parameters and return declared `Int64`, raw i64
  calling convention, used when a call site statically proves `Int64`
  membership for every argument. Generated **only if** the solver proves
  the narrower whole-body claim `args ∈ Int64 → result ∈ Int64` — i.e.
  literally the same check the compiler would run had the developer written
  `foo : Int64 -> Int64` by hand over the same body. This is not new proof
  machinery: it's the existing signature/range-checker, re-run once against
  a synthesized narrower signature.
- a `BigInt = Int - Int64` overload — parameters/return use the tagged
  representation, used otherwise (static proof of non-`Int64` membership,
  or — the common case — no proof either way, resolved by phase 2's runtime
  membership-test dispatch). Present only when the `Int64` overload above
  was generated; otherwise the function stays a single, ordinary `Kind::Int`
  body, and its correctness comes entirely from the separate per-node
  promotion mechanism described above (the "Phase 1's abort branch becomes
  the promotion branch" section) — **not** from this split.

**Why solver-gated, not unconditional (the bug this corrects):** the
original sketch generated an `Int64 -> Int64` overload for *every*
unbounded-`Int` signature unconditionally. That's unsound in general:
`foo : Int -> Int` with `foo(x) = x*x` restricted to an `Int64` *domain*
does not make its *range* `Int64` — `x*x` for `x` near `i64::MAX` vastly
exceeds `i64::MAX`. Phase 2 resolves a call to an overload purely by
argument-domain membership, so a caller who proves `x ∈ Int64` would
dispatch to this overload regardless of what the body computes — and a
body declared `Int64 -> Int64` has, by definition, no tag bit to promote
an out-of-range result into (see the previous section: `Kind::Int64`
never has a tagged representation). It could only wrap silently or abort,
either of which breaks the original `Int -> Int` contract's promise of a
correct result for every input. Gating generation on the solver actually
proving the narrower range claim closes this: when it proves, the
`Int64` overload is *by construction* fully sound end-to-end with zero
tagging anywhere in it (phase 1's existing "proved ⇒ plain instruction"
path applies throughout, unconditionally correct); when it doesn't prove,
no split is generated, and the function relies solely on the always-correct
per-node mechanism instead. There is no in-between case, and consequently
no "known hard part" of tagged locals living inside an otherwise-`Int64`
body — a function either qualifies for a fully-raw split or it doesn't, and
if it doesn't, the split doesn't exist for it at all. Net effect: this
optimization now applies to range-preserving functions (identity, min/max,
bounded arithmetic already provably within range, …), not to every
unbounded-`Int` signature — genuinely-growing functions (`x*x`, naive
Fibonacci, …) still get full completeness from the per-node mechanism,
just without this extra boundary-conversion speedup. Confirmed with Doug:
combined with the tagged-word representation, the common case (values that
never approach the tag boundary) costs nothing beyond one predictable,
never-taken branch per checked operation and zero allocation — matches the
existing phase 1 "proved ⇒ zero cost" character, just gated per-function
here instead of per-node.

This **requires relaxing phase 2's
same-`Kind`-per-position rule** (`check_overload_kind_agreement`,
`semantics/elaborate.rs`) specifically for compiler-generated splits: today
that function only ever sees user-written overload sets and rejects any
`Kind` mismatch unconditionally. The relaxation needs a marker distinguishing
"this pair of overloads is a compiler-generated `Int64`/`BigInt` split" from
an ordinary user-written group, so a genuine user mistake (accidentally
writing two overloads with different parameter `Kind`s) still errors exactly
as it does today. **(DONE — step 2, 2026-07-04; unaffected by this
correction, since the exception itself was always correctly scoped to
`Kind::Int`/`Kind::Int64` pairs regardless of how eligibility for
generating such a pair is decided.)**

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

**Superseded by the solver-gating correction above:** this section used to
describe a "known hard part" where an `Int64` overload's body could still
need tagged locals internally (e.g. `x*x`). That scenario can no longer
arise: generating the `Int64` overload now *requires* the solver to have
proved the whole body stays within `Int64`, so every node inside it is
already known bounded — there is nothing left to tag. A body like `x*x`
that can't clear that bar simply never gets an `Int64` overload generated
for it in the first place, and relies entirely on the per-node mechanism
instead (a single, ordinary `Kind::Int` body, no split involved).

### Step A — whole-function `Int64` promotion (DECIDED and DONE, 2026-07-05)

**Why this exists, and why it was added before step 4b rather than after.**
Cantor's `Kind` doesn't distinguish `Int8`/`Int16`/`Int32`/`Nat`/unbounded
`Int` — every named integer subset elaborates to the same `Kind::Int`
(`kind.rs`). Once step 4b tags every `Kind::Int` value, a blanket
"tag everything" implementation would add a shift-and-tag-check to *every*
integer operation in the language, including values declared over `Int8` or
`Int32` that can never actually need `BigInt` — not just genuinely-unbounded
arithmetic. The overload split above only rescues the narrow case of a bare
unbounded-`Int` domain that *happens* to stay small; it does nothing for the
far more common case of a domain that's already bounded by construction.

**The mechanism.** For any function whose domain is already provably
`⊆ Int64` (any shape — `Int8`, a bounded custom set, `Int64` itself, …, not
just the bare `Int` builtin), there's no "otherwise" case a caller could
ever hit: the ordinary domain-membership proof obligation at every call site
already guarantees every argument fits in `Int64`. So the whole function is
promoted **in place** to `Kind::Int64` — no sibling overload, no runtime
dispatch, nothing for a caller to disambiguate. Concretely
(`src/solver/int64_split.rs`'s `try_promote_to_int64`):

1. Reject anything not already scalar-`Int`-typed throughout (`Bool`/
   `Tuple`/`Vector`/`TaggedUnion` positions never need this; a signature
   mixing `Int` with another Kind is a fast-follow, not this first cut).
2. For each parameter's domain component (`sem_param_set_exprs`), an
   explicit solver entailment check: does a witness value exist that
   satisfies the domain but not `Int64`? Unsat ⇒ proved subset. This is a
   *new* check step 4a's own trial never needed, because step 4a always
   narrows the domain to the bare `Int64` builtin itself as its hypothesis
   — there was nothing else to check.
3. If every parameter clears that bar, build the promoted candidate (same
   body, same *declared* domain/range — only `param_kinds`/`return_kind`
   change to `Kind::Int64`) and run it through the same
   `trial_fully_proves_int64` check step 4a uses (see below).

**MVP eligibility, deliberately narrow like step 4a:** exactly one
signature, no pre-existing overload sibling. Unlike step 4a, no restriction
on arity or on `Mul` — this doesn't synthesize a domain *narrower* than
what's already declared, so there's no new nonlinear-arithmetic bound for
cvc5 to struggle with beyond whatever the function's own declared domain
already required it to handle.

**The eligibility bar, and the step 4a gap it also caught.** It is *not*
enough for the outer `domain → range` contract alone to prove. Two's-
complement `+`/`-`/`*`/`neg` are exact ring operations mod 2^64, so a chain
of only those is safe under raw wraparound hardware as long as the *final*
result is proved in range — wraparound arithmetic computes exactly in
ℤ/2^64ℤ at every step, and if the true final value lands in the unique
`[i64::MIN, i64::MAX]` representative of its residue class, the wrapped
i64 result necessarily equals it, regardless of what happened to
intermediate values (the same reason a checksum is allowed to overflow
mid-computation). But `/` breaks this: dividing an intermediate value that
already wrapped can produce a genuinely wrong quotient even when the true
final answer would have been in range, since division isn't a ring
homomorphism mod 2^64 the way `+`/`-`/`*` are. So both this promotion and
step 4a's split require every individual arithmetic node's own overflow
obligation (phase 1's per-node side channel) to *also* prove `true` for the
trial signature, not just the outer contract — `trial_fully_proves_int64`
inspects the trial's own `overflow_checks` scratch map for this, discarding
it afterward either way (the real per-function loop in `check_file` checks
the eventual replacement item again from scratch and populates the file's
real maps then). **Step 4a's own trial check didn't do this before this
change** — it only checked the outer contract, discarding its scratch
overflow map unused. This is provably fine for step 4a's current shape
(the `Mul`-restriction already forces the body to a `+`/`-`/`/`/`neg`-only
shape... but `/` was *not* excluded, so the gap was real, if narrow and not
known to have an actual failing fixture). Both mechanisms now share the
same stricter helper.

**Behavioural asymmetry this preserves, on purpose.** Once step 4b lands,
an ordinary `Kind::Int` value that overflows i64 *promotes to a boxed
`BigInt` and keeps computing correctly* — it never aborts. A function
promoted to `Kind::Int64` by this mechanism has no tag bit to promote into,
so if it ever did overflow it could only abort (phase 1's existing
behaviour, unchanged). Requiring every arithmetic node to independently
prove `Int64`-bounded is what makes this safe: a function that qualifies
genuinely never needed the `BigInt` safety net in the first place, so
opting it out of that net costs it nothing; a function that doesn't qualify
keeps the full tagged/`BigInt` treatment. Before step 4b exists, `Kind::Int64`
and `Kind::Int` compile identically (both raw i64, both driven by the same
per-node `overflow_checks` proved/unproved decision) — promotion is
observably inert until step 4b lands, confirmed by the full existing test
suite (920 tests, unit + integration) passing unchanged. Tested in
`tests/solver/int64_split.rs`: single- and multi-parameter and zero-
parameter bounded domains promoting without a split; an unbounded `Nat`
domain declining; a domain that's *itself* exactly `Int64` but whose body
(`x + x`) can still overflow declining (the case a "final result in range
alone" check would miss); and a promoted function's callers still proving
with a plain direct call, no dispatch.

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
3. **Solver — DONE (2026-07-04), confirmed no-op for the ℤ reasoning itself,
   plus one incidental bug fix found while auditing.** The overflow
   obligation (`OverflowObligation`, `solver/encode.rs`) is encoded purely
   from the CVC5 *sort* (`term.sort().is_integer()`), never from `Kind` —
   confirmed by reading `encode_unop`/`encode_binop` directly — so it already
   generalizes to a future `Kind::Int64` position with zero changes, exactly
   as the original sketch assumed.

   Audited every other `Kind`/`ValKind` match in `src/solver/` for the same
   "would this silently mishandle `Kind::Int64`" question the exhaustive-match
   compiler errors already answered for step 2 (those only catch *missing*
   arms, not a wildcard/deny-list arm that happens to be wrong). Found one:
   `disjointness.rs`'s `fresh_overload_param_terms` used an explicit
   **allow-list** (`ValKind::Bool`, `ValKind::Int`, else `Err("non-scalar
   ... not yet supported")`) to build fresh comparison terms for the
   phase 2 overload-disjointness proof — the one deny-list-shaped exception
   among otherwise deny-list-style matches elsewhere (`mod.rs`,
   `encode_call.rs`, `membership.rs`, `blocks.rs` all check for specific
   *other* Kinds and fall through to integer treatment by default, already
   correct). A future `Kind::Int64` parameter — exactly what the phase 3
   split's fast overload will have — would have hit the `Err` arm and wrongly
   reported "cannot verify overload disjointness: non-scalar parameter
   positions are not yet supported", even though it's a plain scalar
   integer. Fixed to `ValKind::Int | ValKind::Int64 => ...`, matching
   `sort.rs`'s existing pattern. Left untested in isolation (deliberately):
   nothing produces `Kind::Int64` anywhere yet, so this exact branch is
   unreachable dead code until step 4 exists, and step 4's own end-to-end
   CLI tests (a real `Int64`/`BigInt` split checked for disjointness through
   the normal `check_file` pipeline) will be the first thing to actually
   exercise it — building the fixture-based plumbing step 2 used, purely to
   cover an unreachable branch in isolation, wasn't judged worth it here.
4. **Codegen** (4a is really a pre-codegen semantics/solver pass — it decides
   *whether* a split exists at all before any of 4b–4d's codegen work
   applies — but stays numbered under step 4 since it only matters once
   codegen is the consumer). **Step A (whole-function `Int64` promotion,
   DONE 2026-07-05, see its own section above) runs first**, in the same
   `src/solver/int64_split.rs` pass: a name is only handed to 4a's split
   logic once promotion has already declined it.
   a. **Split-generation pass — DONE (2026-07-04)**, in
      `src/solver/int64_split.rs`, inserted in `check_file` between
      `elaborate()` and the main per-function loop. For each user
      `SemFunctionDef` whose declared domain and range are *both* the bare
      unbounded `Int` (MVP scope: single parameter, single signature, no
      pre-existing overload sibling of the same name, and — see "Known
      issues" below — a body containing no `Mul`): synthesize an
      `Int64 -> Int64` narrowed signature over the *same* body and check it
      in isolation via the ordinary existing signature/range-checker
      (`check_function`, already `pub`), with the candidate's own `fn_env`
      entry overridden to the narrowed signature so a recursive self-call
      uses it as its own induction hypothesis (confirmed necessary and
      sufficient with a dedicated test — see below). If it proves: replace
      the original item with **two** `SemFunctionDef`s, both
      `compiler_generated_split = true` — the `Int64` one just checked, and
      a `BigInt`-named overload whose *domain* is `Int - Int64` (for phase
      2 disjointness) but whose *range* is the **original**, unrestricted
      `Int` (not also narrowed to `Int - Int64` — that was a bug caught by
      the test suite: narrowing the range too is false in general, e.g.
      halving a value just outside `Int64` can land back inside it) — and
      let every downstream step (disjointness, per-function checking,
      codegen dispatch) treat them as an ordinary phase 2 overload pair,
      unchanged. If it doesn't prove: leave the original `SemFunctionDef`
      exactly as-is, untouched — no split, no `compiler_generated_split`
      marker, single ordinary `Kind::Int` body. Tested in
      `tests/solver/int64_split.rs`: the split firing and both overloads
      proving; a genuinely non-Int64-preserving function *not* splitting
      while the file still proves overall; non-bare-`Int` domains,
      multi-signature functions, and names with a pre-existing user
      overload all correctly left alone; the recursive induction-hypothesis
      override actually being load-bearing (a converging recursive
      function that provably stays in `Int64` only *because* the self-call
      uses the narrowed contract); and the split pair dispatching through
      phase 2's ordinary static-resolution machinery unchanged.

      **Known issue found while implementing (pre-existing, not part of
      this step, deliberately not fixed here):** bounding a `Mul` node to
      `Int64` in the trial check was found to make cvc5 run for 90+ seconds
      past even a 2000ms `tlimit` — investigating further showed this isn't
      actually specific to `Int64` or to this step at all: `f : Nat -> Int;
      f(x) = x * x` (no relation to this split — bare pre-existing phase 1
      machinery, `Nat` domain, nothing here touches it) hangs the same way,
      while `f(x) = x * y` (two independent variables, already covered by
      existing tests) is fast. So cvc5 apparently struggles specifically
      with a *self*-multiplication (`x * x`) under a bounded existential,
      regardless of which bound. This is a real, shippable-today bug
      (anyone writing `x * x` in a domain-bounded function can already hang
      the compiler) that predates phase 3 entirely and was only surfaced
      here by chance (no existing test happened to self-multiply a
      variable). Mitigated *for this step only* by skipping the trial
      check entirely whenever a candidate's body contains any `Mul` node
      (`int64_split.rs`'s `body_contains_mul`) — a background-thread
      watchdog was considered and rejected: cvc5 isn't thread-safe even
      with per-thread `TermManager`/`Solver` instances (`CVC5_CALL_LOCK`'s
      doc comment), so racing a second concurrent cvc5 call while
      abandoning a hung one risks a segfault, not just wasted time. Logged
      here rather than fixed now, per Doug — candidate next steps once
      picked up: try cvc5's `--nl-ext`-family options, or encode `x * x` as
      a fresh term with an asserted non-negativity fact rather than a raw
      product. Whoever picks this up should also lift step 4a's `Mul`
      restriction once it's resolved.
   b. **Attempted 2026-07-04, reverted mid-session — "scalar only, defer
      call boundaries" is not a viable slice boundary.** Original plan:
      tagged encode/decode at every unbounded-`Int` value's construction/
      consumption site (literals, arithmetic results, comparisons,
      printing), deferring vector/struct/tuple elements *and* call-boundary
      coercion to later slices. Landed literal/arithmetic/comparison
      tagging (`cantor_bigint_*` calls in `compile_arith`, a new
      `cantor_bigint_to_i64` decode entry point, `runtime_decls.rs`/`jit.rs`
      wiring) and tested against a real multi-function CLI program
      (`run_demo.cantor`: `double(abs(-21))`) — **immediate crash**, nothing
      to do with the split. `double`'s `Kind::Int` parameter is now
      "tagged" by convention, but `compile_call` (untouched) still passes
      the caller's raw, untagged result of `abs(-21)` = -21; being odd,
      its low bit reads as "pointer to a boxed BigInt", and the runtime
      dereferences garbage. Nearly every test in the suite calls at least
      one helper function, so call-boundary coercion isn't a rare edge case
      to defer — it's the overwhelming common case, and can't be separated
      from literal/arithmetic tagging even for a "scalar only" cut. Reverted
      `codegen/expr.rs`'s tagging changes back to today's raw-only
      behaviour; kept the inert prep work (the new runtime function +
      tests, the declarations, and an independent, already-latent
      parameter-binding bug this surfaced — see below) since none of it
      changes behaviour on its own. All 704 tests green again as of this
      revert.

      **Independent bug found and fixed while investigating (kept,
      unrelated to the revert):** `compile_function_body`/
      `compile_block_body` (`codegen/mod.rs`) hardcoded `Kind::Int` when
      binding *any* non-Bool/Tuple/TaggedUnion/Vector/Set parameter into
      `env`, discarding the actual declared `Kind`. Harmless before
      `Kind::Int64` existed (both compiled identically), but would have
      silently mislabelled a compiler-generated `Int64` overload's own
      parameter as `Kind::Int` the moment any codegen logic started caring
      about the difference. Fixed to preserve `kind.clone()`.

      **Real scope, confirmed empirically:** call-boundary coercion (tag a
      raw arg for a `Kind::Int` param; decode a tagged arg for a resolved
      `Int64` param; the dispatch-merge return-Kind bug already identified)
      has to land *together* with literal/arithmetic/comparison tagging and
      CLI/JIT output decode — there is no smaller correct increment than
      "every place a scalar `Kind::Int` value is produced, consumed, or
      crosses a function boundary, all at once." Confirmed and landed this
      way on 2026-07-05 — see the full writeup below ("Step 4b —
      tagged-value codegen").
   c. **DONE (2026-07-05).** Phase 1's abort branch is now the promotion
      branch for every tagged `Kind::Int` arithmetic node — see below;
      bounded-`Int64` nodes (Step A/step 4a raw arms) keep the phase 1
      abort, unchanged, exactly as designed (they're proved never to need
      it).
   d. **DONE (2026-07-05).** Comparisons (`<`, `<=`, `==`, …) route through
      `cantor_bigint_cmp` whenever either operand is tagged; printing
      (`main.rs`'s scalar/tuple-leaf output, `?` narrowing's Fail-wire
      payload) routes through `cantor_bigint_to_string` on the boxed tag
      bit. The both-small fast-path-inside-the-runtime-function optimization
      (skip `cantor_bigint_cmp`'s own call overhead with an early tag check
      *in codegen* before calling it) was **not** done — deferred as a minor
      follow-up since it doesn't affect correctness, only shaves one
      avoidable call on an already-not-statically-elided check.
5. **Tests / docs — DONE (2026-07-05) for the core surface**: CLI e2e
   covering (ii) a call that overflows i64 promotes and continues to a
   correct (if now BigInt-backed) result instead of aborting
   (`tests/cli/overflow.rs`, rewritten from phase 1's abort-expecting
   originals); comparisons, call boundaries, runtime dispatch mixing an
   Int64/BigInt split, and domain-membership checks on boxed values
   (`tests/cli/bigint.rs`, new). **Still open:** (i) a call proved `Int64`
   compiles to the raw overload with no promotion codegen at all, asserted
   directly on emitted IR; (iv) `require`/`assert ... not in BigInt` once
   `BigInt` is exposed as an ordinary named set (see below) — neither is
   blocking, both are fast-follow coverage. README: retire the "Known
   incompleteness" call-out for *scalar* `Int`/`Nat` — closed by this step
   — but add a narrower one for `Vector(Int)`/`Set(Int)` (see below, still
   open). design-decisions.md: promote this section's representation choice
   from this doc into §7's Integers subsection as DECIDED (small pointer,
   full detail stays here) — not yet done.

### Step 4b — tagged-value codegen (DONE, 2026-07-05)

Landed as one cohesive change, per the "real scope" finding above and the
decision to fold call boundaries in rather than re-attempt a smaller slice
(confirmed with Doug via `AskUserQuestion` before starting). The scope grew
twice more while implementing, each time surfaced by an actual failing test
rather than assumed up front — recorded here so the next person touching
this code understands *why* the surface is shaped the way it is, not just
*that* it is.

**The key design decision: tagging is gated on `Compiler::tagging_active()`
(`overflow_ctx.is_some()`), not unconditional.** `compile_file`/
`compile_items` (the REPL, the `llvm-ir` subcommand, and every direct-codegen
unit test in `tests/codegen/*.rs`/`tests/solver/*.rs`) never run
`int64_split`'s Step A/4a passes — nothing in that pipeline ever produces a
`Kind::Int64` position, so there's nothing for a tagged `Kind::Int` to be
mixed with, and no need to change that pipeline's ABI at all. Discovered the
hard way: an early version tagged unconditionally, and the entire
`tests/codegen` binary either corrupted values (a raw i64 count from
`len()`/`size()`, or a raw `Set`/`Vector(Int)` element, reinterpreted as a
tagged word) or crashed outright (`as_bigint` null/misaligned-pointer
dereference on a bit pattern that was never actually a tagged word in the
first place) — over a hundred existing tests assume a plain-i64 JIT ABI for
`fn(i64) -> i64`-shaped test helpers, and rewriting all of them was both far
outside this step's scope and unnecessary once the real fix (gate on
`tagging_active`) was found. `ensure_tagged`/`ensure_raw_int64` (the
encode/decode primitives) and `compile_tagged_i64_const` (literal encoding)
are no-ops when `!tagging_active()`; `compile_membership`'s `tagged`
parameter is ANDed with it at the function's entry so no caller has to
remember to. This is also why the "raw path" in `compile_arith`/
`compile_unop` reports `Kind::Int` (not `Kind::Int64`) when tagging isn't
active — outside the verified pipeline `Kind::Int64` never appears anywhere
at all, and a stray one would break the very `TaggedUnion`-arm matching
(`coerce_to_kind`) that surfaced this bug.

**Scope, confirmed by iterating against real failures:**
- **Literals** (`compile_tagged_i64_const`, `codegen/coerce.rs`): a bare
  literal's default representation comes from `Compiler::current_bare_int_kind`
  — `Int64` only inside a Step-A-promoted/step-4a-split body (nothing else
  to inherit from, unlike every other expression kind, which propagates an
  upstream Kind). Small values (`runtime::TAG_SMALL_MIN..=TAG_SMALL_MAX`,
  one bit narrower than `Int64`) fold to `n << 1` at compile time; the rare
  literal outside that range boxes via a runtime `cantor_bigint_from_i64`
  call — the *only* place a literal can end up boxed, confirmed the lexer
  already rejects anything wider than `i64`.
- **Arithmetic/comparisons/unary `-`** (`codegen/arith.rs`, extracted from
  `expr.rs` as a same-session pure refactor once the file crossed 1000
  lines again): routes through `cantor_bigint_{add,sub,mul,div,neg,cmp}`
  whenever either operand is genuinely tagged; two operands that are *both*
  raw `Int64` stay on phase 1's existing checked/proved-elide path,
  unchanged. `ensure_tagged` reconciles a mixed pair (e.g. a Step-A-promoted
  call's raw result combined with an ordinary tagged local) before combining.
- **Call boundaries, both directions, found incrementally:**
  - Call *arguments* (`compile_call`, `expr.rs`): tag/untag when the
    argument's representation doesn't match the callee's declared param
    Kind.
  - Call/function *returns* — **the first thing that actually broke**,
    exposed by `main() = combine(100)` where `combine` (ordinary, tagged)
    calls `add8` (Step-A-promoted, raw): nothing coerced the body's computed
    Kind against the function's own declared return Kind at the return
    boundary itself. Fixed with a new `coerce_int_return`
    (`codegen/coerce.rs`), wired into *all three* return sites —
    `compile_function_body`, `compile_block_body`, **and** the early
    `return` statement path (`compile_return_stmt`, `blocks.rs`) — the
    third one doesn't get the Vector/TaggedUnion return coercions either
    (a separate, pre-existing, out-of-scope gap), but keeping it consistent
    for Int/Int64 specifically was cheap and avoided introducing a new
    inconsistency.
  - `if`/`else` branch merging (`kind::merge_if_branches`, `codegen/expr.rs`'s
    `compile_if`) needed a new `IfMerge::CoerceInt64ToInt` variant for the
    same reason — one branch calling a promoted function, the other not.
- **Overload dispatch** (`codegen/overload_dispatch.rs`): a `Dispatch`
  call's shared argument representation is canonicalized to tagged `Int`
  (mapping any `Int64` position from the "representative" candidate) — this
  is what the domain-membership pre-check and the `phi` merge both need a
  common representation for. Each candidate's own args are decoded back to
  its *real* declared Kind (`fn_param_kinds`) immediately before its call;
  each candidate's result is re-encoded to tagged before the `phi`.
- **`Vector(Int)`/`Set(Int)`/runtime-`Set` `for`-loop storage — deliberately
  stays raw, decode-on-read/encode-on-write at the boundary.** This is an
  explicit, documented scope line, not an oversight: making container
  *elements* genuinely arbitrary-precision would need a canonical (i.e.
  never-duplicated) tagged representation for `Set` dedup/equality — two
  *different* boxed heap allocations holding the same integer are not
  `==` as raw pointers, so `cantor_set_insert_i64`/`cantor_set_contains_i64`
  would silently break set semantics the moment a boxed value entered a
  set. Out of scope for this pass; `ensure_raw_int64`/`ensure_tagged` at
  each construction/read site (`compile_tuple_as_vector`,
  `compile_scalar_as_singleton_vector`, `compile_index`/`compile_proj`,
  `compile_set_lit_value`, `compile_runtime_contains`, `compile_for_in`'s
  runtime-set loop) mean a value that doesn't fit raw `Int64` aborts loudly
  (via `ensure_raw_int64`'s existing "compiler invariant violated" message —
  imprecise wording for this specific case, noted as a TODO) rather than
  corrupting anything. `Tuple`/`TaggedUnion` payload leaves needed **no**
  changes at all — they already pass an `Int` position's bits through
  opaquely, so whatever representation it already is (tagged or raw) just
  carries through unchanged.
- **Domain/range membership checks** (`codegen/membership.rs`): every
  `IntBound` arm (`NonNeg`/`Positive`/`NonZero`/`Bounded`) and the
  named-set/set-literal equality arms now route through a new
  `compile_int_cmp_const`, which for a tagged value compares the *small*
  case (order-preserving under the `<< 1` shift — comparing both operands
  shifted the same way preserves `<`/`=`/`>`, so this needs no unshifting)
  via a `select` against the *boxed* case (`cantor_bigint_cmp`) on the tag
  bit. Found by tracing exactly why a raw bit-pattern comparison against an
  unshifted bound (e.g. `Int8`'s `127`) is wrong for *any* tagged value, not
  just a boxed one — `100` (valid `Int8`) tags to `200`, and `200 <= 127` is
  false.
- **Builtins/constants that returned or passed through a raw value under
  the tagged `Kind::Int` label — the second thing that actually broke**,
  exposed by `len(foo())` crashing (a `Kind::Int64`-shaped null-pointer
  dereference from a `len()` result that was never tagged in the first
  place, hit only once a *caller* — `main`, promoted by Step A — tried to
  coerce it as if it were a mismatched `Int64` value). Fixed: `len()`/
  `size()` now tag their raw runtime-function count before returning;
  `from(x)`/the auto-generated `distinct` constructor now preserve the
  argument's actual Kind instead of hardcoding `Kind::Int` (a pure
  pass-through has nothing to tag); named scalar constants
  (`compile_elaborated`'s pass-0 constant folding, `codegen/mod.rs`) are
  now encoded through `compile_tagged_i64_const` instead of a bare
  `const_int`.
- **Fallible functions are explicitly out of scope for Step A promotion**
  (`int64_split.rs`, one added guard): a `SemFunctionDef`'s `return_kind`
  names only the success Kind — `Fail`-ness lives entirely in the
  `{i1, i64}` wire struct built separately at the codegen boundary — so
  promoting one would need the success payload's raw-vs-tagged
  representation threaded through that wire too. Not done; fast-follow.
- **Output decode**: `main.rs`'s scalar/fallible/tuple-leaf `main` display
  paths, and the fallible-`main` error-code path, all decode through a new
  `format_tagged_int` when the relevant Kind is `Int`. The REPL's own
  `evaluate_expr` print does **not** — it goes through `compile_file`, so
  `tagging_active()` is always `false` there and the result is already
  plain, exactly as before this step.

**What's still open, deliberately deferred:** the emitted-IR assertion for
a proved-`Int64` call eliding all promotion codegen; `require`/
`assert ... not in BigInt` (needs `BigInt` exposed as an ordinary named
set, `BigInt = Int - Int64`, itself deferred); the both-small early-exit
codegen optimization for `cantor_bigint_cmp` call sites; a clearer abort
message for the `Set`/`Vector(Int)` "doesn't fit raw i64" boundary case.

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
