# Wrapping fixed-width integers and quotient sets: plan

**Status: design drafted 2026-07-05, not yet implemented.** Three open forks
were resolved with Doug before writing this:

1. `Signed32`/`Unsigned32` are **fully disjoint from each other**, not just
   from `Int` — each gets its own opaque solver sort, not a shared bit
   pattern space. (Mirrors the existing, deliberate `Bool`≠`Int` stance —
   see `feedback_bool_int_disjoint` in project memory: two representationally
   identical bit patterns must not become solver-equatable just because
   nothing else keeps them apart.)
2. `rem`/`quot` use **Euclidean** semantics (`rem` always `0 <= rem < |d|`),
   not truncating. This is what makes the motivating
   `IntMod5 = Int / (x -> x rem 5)` example land in a clean canonical range
   with no fixup, and it's also what cvc5's native integer division/modulus
   already computes natively — see the "why this matters" note under
   Feature 2.
3. Quotient-set formation requires the compiler to **prove the canonicalizer
   is idempotent** (`f(f(x)) == f(x)` for all `x ∈ L`); if unproved, that's a
   **hard compile error**, no `assume` escape hatch — same category as
   recursive-set well-foundedness (§3 of design-decisions.md), not the
   ordinary graduated assert/assume obligation used for domain/range checks
   generally.

This doc is detailed enough to work from directly, following CLAUDE.md's
parser → semantics → solver → codegen staging. Confidence levels are called
out inline — several corners (exact cvc5 int-to-bitvector API, exact
auto-constructor plumbing) need a small implementation spike before the
sketch below can be trusted verbatim; those are flagged, not glossed over.

---

## Where this sits

Both features extend the numeric tower documented in design-decisions.md
§13 and built out in int-soundness-plan.md (`Int`/`Int64`/`BigInt`). Neither
reuses that machinery directly — `Int64`/`BigInt` is a **codegen
representation split** on top of the single mathematical set `Int`, whereas
`Signed32`/`Unsigned32` are **new, genuinely distinct sets** (like `distinct`
today), and quotient sets are a **new named-subset former** (like a
predicate-defined set). The real precedent for both is the `distinct`
mechanism (`src/solver/mod.rs`'s `build_distinct_preds`, `DistinctInfo` in
`src/solver/membership.rs`) — a CVC5 uninterpreted sort plus
constructor/destructor uninterpreted functions, basis obligations emitted
on demand, no global axioms.

**Surprising finding, worth stating up front:** these two features are less
coupled than the original framing suggested. Tracing the actual code showed
`A / B` in set-expression position is *already* parsed and elaborated into
its own node (`SemExprKind::SetQuotient`, `src/semantics/tree.rs:50`,
produced by `src/semantics/elaborate/binop.rs:105`) — distinct from
value-position `Div` from the start, specifically so a future quotient-set
feature would have a clean hook. Every consumer today
(`src/solver/sort.rs:369`, `src/solver/encode.rs:328`,
`src/solver/disjointness.rs:92`, `src/codegen/expr.rs:56`,
`src/solver/int64_split.rs:453`) either panics or returns a hard `Err` on
it — correct, fail-loud placeholders per CLAUDE.md's item 0, not bugs.
Quotient sets, staged the way Doug described (named-function canonicalizer
only, no operator derivation), turn out to need **no new solver sort and no
codegen at all** — see Feature 2 below. Feature 1 is the larger, more
solver-novel piece. Suggested sequencing at the end reflects this.

---

## Feature 1 — `Signed32` / `Unsigned32` (wrapping fixed-width integers)

**Status: DONE, 2026-07-06.** Landed close to this sketch — the spike
resolved every medium-confidence unknown flagged below in favor of the
sketch's own guesses (see "Resolved during implementation" just below) — but
two real gaps this doc didn't anticipate were found and fixed along the way:

1. **The `Int ↔ BitVec` spike confirmed everything hoped for, with zero
   surprises.** A standalone probe against the real `cvc5` crate (mirroring
   this doc's suggested spike) confirmed: `Kind::IntToBitvector` handles
   arbitrary integers (negative, or ≥ 2^32) with the mod-2^32 reduction done
   *internally* by cvc5 — no manual pre-reduction formula needed, resolving
   the doc's first open question. `Kind::BitvectorUbvToInt` and
   `Kind::BitvectorSbvToInt` both exist natively in the installed cvc5
   1.3.1 — no hand-rolled `ite` needed for the signed reading either,
   resolving the second and third open questions. All three "needs a spike"
   items below turned out to need no compromise at all.
2. **Elaboration's value-position `+ - * neg`/comparisons hard-coded
   `Kind::Int`, not traced by this doc.** `binop.rs`'s `Add`/`Sub`/`Mul`
   (value position) and `expr.rs`'s `UnOp::Neg` unconditionally produced
   `Kind::Int` regardless of operand Kind — harmless historically, since
   every existing operand Kind those paths ever saw genuinely was `Kind::Int`
   (even `distinct` values, whose Kind is always `Int` by design). Once an
   operand can genuinely be `Kind::Signed32`/`Kind::Unsigned32`, this
   default would silently mislabel the result — the same "plausible-looking
   wildcard default" trap this doc's own `builtin_call_kind` note already
   warned about, just at a different call site the doc didn't trace this
   far. Fixed by deriving the result Kind from the operands (same Kind in →
   same Kind out; falls back to `Int` for every other combination, exactly
   preserving prior behavior for everything that isn't wrapping). Ordered
   comparisons got the analogous fix (`is_ordered_pair`, generalizing the
   old "both operands must be `Int`" check to "both operands the same one of
   `Int`/`Signed32`/`Unsigned32`").
3. **The pre-existing `binary_builtin_domain`/`unary_builtin_domain`
   "operand must be Int" obligation had to be checked *after* the new
   wrapping encoding, not before.** These built-in domain obligations
   (`obligations.rs`) run unconditionally for every `Add`/`Sub`/`Mul`/`Neg`
   node, regardless of operand Kind — previously harmless, since a
   `distinct` value's Kind is always `Int` so the obligation never actually
   fired for it. A `Signed32`/`Unsigned32` operand is genuinely never a
   member of plain `Int`, so encoding the domain check *before* the new
   `bv*` path (the natural place to slot it in) made every wrapping
   arithmetic expression a spurious counterexample — caught by the CLI
   tests, fixed by moving `encode_wrapping_binop`/the `Neg` wrapping check
   earlier, ahead of that obligation loop, so a same-family wrapping pair
   returns before the "must be Int" domain check ever runs.
4. **`signed32(n)`'s constructor and `from(x)`'s destructor needed the
   existing tagged/raw-`Int` conversion helpers** (`ensure_raw_int64`/
   `ensure_tagged`, int-soundness-plan phase 3), not a bare `trunc`/`sext`:
   the `n : Int` flowing into `signed32(n)` may be the tagged small-int
   representation (or a boxed `BigInt`), not a raw i64 word, so truncating
   it directly produced silently wrong bit patterns until untagged first.
   Symmetrically, `from(x)`'s sign-/zero-extended `i64` needs tagging before
   it's a valid `Kind::Int` value. Caught by the CLI tests (`Signed32`
   arithmetic on literals like `-2147483648` produced wrong values until
   this was fixed — `Unsigned32` tests with only positive/small literals
   happened not to exercise the tagging path, which is why this wasn't
   caught immediately).

No new `BuiltinKind`/registry-generalization abstraction was needed beyond
what's sketched below — `semantics::builtins::lookup` already generalizes
via `Kind`, so `Signed32`/`Unsigned32` slot in as two more match arms next
to `Bool`/`Fail` with no new enum. `arm_ctor_name`/`arm_ctor_name_for_arm`
likewise needed no disambiguation logic beyond a name each, since — unlike
`distinct` sets, which all share `ValKind::Int` — `Signed32`/`Unsigned32`
already have their own unique `Kind`, so cross-kind-union arm naming was
automatically collision-free.

### Scope for this slice

Only width 32, both signed and unsigned, and only `+ - * neg` plus
comparisons. Division/remainder on wrapping sorts is deferred (division
isn't a ring homomorphism mod 2^N, same lesson int-soundness-plan.md's
"why solver-gated" section already drew for `Int64`/`BigInt` — a genuinely
separate follow-on, not bundled in). Additional widths (`Signed8`,
`Signed16`, `Signed64`, ...) are a mechanical repeat of this slice once it
lands, not attempted up front.

**Naming, medium-confidence recommendation:** ship `Signed32`/`Unsigned32`
as hardcoded builtins (parallel to how `Int8`..`Int64` are hardcoded name
lookups in `semantics/builtins.rs` today), not via a new general-purpose
`wrapping` keyword users could apply to arbitrary widths. Reasoning: a
generalized modifier keyword is extra parser/semantics surface with no
second use case yet, and the internal machinery below (a distinct-sort
wrapper over a bit-vector basis) is exactly as reusable later if a
`wrapping` keyword does turn out to be wanted — nothing is lost by starting
concrete. Flagging this as a recommendation rather than a settled decision
since it wasn't one of the three forks explicitly discussed.

### The key architectural decision: BitVec-backed, not Int-backed

The generic `distinct` sort has **zero arithmetic defined on it today** —
confirmed by reading `src/solver/encode.rs`: the `BinOp` sort-mismatch guard
returns a dummy value for any non-integer-sorted operand and relies entirely
on `Membership::Constrained(false)` obligations to reject the program.
Reusing that as-is for Signed32 would mean hand-deriving two's-complement
wraparound using `Int` arithmetic (explicit `mod 2^32` formulas at every
operation) — reinventing exactly what CVC5's native bit-vector theory
already provides as a *definitional* property, not a proof obligation.
`bvadd`/`bvsub`/`bvmul`/`bvneg` wrap by construction; there is nothing to
prove and nothing that can time out.

So: represent the sort as CVC5's native `(_ BitVec 32)`, but — per fork 1 —
each of `Signed32`/`Unsigned32` still needs its own **fresh uninterpreted
sort** on top, exactly the way `distinct` wraps `Int`, so the two (and `Int`
itself) stay mutually opaque to the solver. Concretely:

```rust
struct WrappingInfo<'tm> {
    width: u32,
    signed: bool,
    bv_sort: Sort<'tm>,   // (_ BitVec width) — shared/cached per width
    d_sort: Sort<'tm>,    // this name's own fresh uninterpreted sort
    mk: Term<'tm>,        // BitVec(width) -> D   (uninterpreted)
    from: Term<'tm>,      // D -> BitVec(width)   (uninterpreted)
}
```

The critical choice is **what `mk`/`from` connect to**. `DistinctInfo`
today connects straight to `Int` (`mk_D : Int -> D`). Doing the analogous
thing here (`mk_D : Int -> D`, with `D` secretly meaning "a bit-vector
value") would force every arithmetic op to round-trip through `Int ↔
BitVec` conversions (`int2bv`/`bv2int`), which are exactly the
non-injective, solver-unfriendly conversions worth avoiding — and would put
them on the *hot path* (every `+`), not just at genuine `Int`-boundary
crossings.

Instead, connect `mk`/`from` **directly to `BitVec(width)`**:
`mk_D : BitVec(32) -> D`, `from_D : D -> BitVec(32)`. Then:

- **Arithmetic between two same-family operands** (`x + y` where both are
  `Signed32`, or both `Unsigned32`): `from_D(x)`, `from_D(y)` — now
  bit-vector terms — combine via `bvadd`/`bvsub`/`bvmul`/`bvneg` directly,
  then `mk_D(result)`. No `Int` involved anywhere in this path. This is
  *simpler* than checked `Int` arithmetic: no overflow obligation, no
  `BuiltinObligation`, no counterexample branch — wrapping is what the
  operator means, definitionally, so there's nothing to check. This
  confirms your intuition that this part is easy.
- **Equality/inequality** (`==`, `!=`) between two same-sort `D` terms:
  plain term equality, no unwrap needed at all — two ground terms of an
  uninterpreted sort are solver-equal exactly when they denote the same
  value, which is already the right meaning for `==` here. (Generic `BinOp`
  encoding already doesn't special-case sorts for this, so likely zero new
  code — confirm during implementation.)
- **Ordered comparisons** (`<`, `<=`, `>`, `>=`): route to `bvslt`/`bvsle`/…
  for `Signed32`, `bvult`/`bvule`/… for `Unsigned32`, applied to
  `from_D(lhs)`/`from_D(rhs)`. This is the one place signed vs. unsigned
  actually changes which CVC5 operator gets used.
- **The only place `Int ↔ BitVec` conversion is needed at all**: the
  user-facing constructor (`signed32(n)` for `n : Int`) and destructor
  (`from(x)` back to `Int`) — exactly two conversion points, not on every
  operation. `signed32(n)`'s conversion is total (always succeeds — see
  below); `from(x)`'s is total in the other direction too.

**Medium confidence, needs a spike before committing:** the exact CVC5
API/`Kind` names for `Int → BitVec` and `BitVec → Int` conversion, and
whether cvc5 requires the integer already reduced to `[0, 2^32)` before
`int2bv`, or handles arbitrary integers itself. Do a small standalone probe
against the `cvc5` crate directly first — same pattern the BigInt plan used
for the `nl-cov` investigation (`docs/int-soundness-review-2026-07-05.md`'s
reproduction script is the template to copy). Concretely to verify:
- `Int -> BitVec(32)`: need `((n mod 2^32) + 2^32) mod 2^32` (Euclidean,
  always non-negative) fed into whatever cvc5 calls its int-to-bitvector
  operator, or confirm cvc5 already handles this internally.
- `BitVec(32) -> Int`, unsigned reading (`Unsigned32`'s `from`): cvc5's
  `ubv_to_int`-equivalent, or hand-rolled if unavailable in the installed
  cvc5 1.3.1 (`Cargo.toml`'s pin).
- `BitVec(32) -> Int`, signed reading (`Signed32`'s `from`): either a native
  `sbv_to_int`-equivalent, or hand-roll
  `ite(bv[31] == 1, ubv_to_int(bv) - 2^32, ubv_to_int(bv))` — straightforward
  either way, just needs confirming which path exists.

### Integration point already found: the cross-kind union detector

`src/solver/sort.rs:322` builds `is_distinct_sort` as a closure keyed
directly off `distinct_preds.values()`. If wrapping sorts live in a
separate `WrappingPreds` map (as sketched above), this closure needs to
also check that map — or, cleaner, the two registries get unified behind
one "is this an opaque/uninterpreted sort" query so `Signed32 | Int`,
`Signed32 ^ Unsigned32`, etc. get the existing "genuinely disjoint" cross-kind
union treatment for free, with zero changes to the union-datatype builder
itself (same reasoning as the `Fail`-as-distinct-sort work — see
`project_fail_distinct_sort` memory).

### Semantics-layer traps to avoid (found by reading the actual code, not assumed)

`src/semantics/elaborate.rs:178-192`'s `builtin_call_kind` is where
`litre(n)`'s auto-generated constructor is recognized today (capitalize the
callee, look it up in `name_defs`, check `DefKind::Distinct`) — and it
**always returns `Kind::Int`**, which is correct for `distinct` (recall:
`distinct` never creates a new Kind, per the value-layers design — `Litre`
maps to the same Kind as its basis). **This is subtly wrong if copy-pasted
for wrapping sorts**: `signed32(n)`'s result must have Kind `Kind::Signed32`,
not `Kind::Int` — unlike `distinct`, a wrapping sort genuinely does get its
own runtime Kind (different LLVM width, different ABI extension). This
function needs to become sensitive to *which* registry the def belongs to,
not just whether one exists — a concrete place a naive generalization would
silently produce the wrong Kind (exactly the "plausible-looking wildcard
default" antipattern CLAUDE.md's item 0 warns about).

`from`'s recognition (`src/semantics/elaborate.rs:184`, and the solver-side
analog at `src/solver/encode_call.rs:40-83`) is, by contrast, **already
correct as a shared path**: `from(x)` destructing either a `distinct` value
or a `Signed32`/`Unsigned32` value both genuinely produce `Kind::Int` /
land back in `Int` at the solver layer, so this one code path should extend
to wrapping sorts with no Kind-correctness changes, just an added lookup
into the wrapping registry alongside `distinct_preds`.

### Codegen (confirms your intuition — this really is the easy part)

- New concrete `Kind` variants: `Kind::Signed32`, `Kind::Unsigned32` (flat
  variants, not a parameterized `Kind::Wrapping{width,signed}` — mirrors how
  `Kind::Int64` was added as one concrete variant rather than a generic
  width parameter; every `Kind` match in the compiler is exhaustive today,
  so a payload-carrying variant would touch every destructuring site for no
  benefit at this scale).
- LLVM representation: plain `i32` register, **no** `nsw`/`nuw` overflow
  flags on `add`/`sub`/`mul` — LLVM's default `i32` arithmetic is already
  exactly two's-complement wraparound, so there is genuinely zero
  overflow-intrinsic plumbing to write, unlike checked `Int` arithmetic.
  Unary negate is `sub i32 0, x` (also wraps correctly at `i32::MIN`, no
  guard needed — this is the entire point of "wrapping is the intended
  semantics" as opposed to `Int`'s checked-then-abort/promote model).
- ABI boundary: reuse the existing "every value crosses as `i64`" convention
  (same one `Bool` already uses: `i1` internally, widened/truncated at
  call/return boundaries). `Signed32` sign-extends `i32 -> i64` on the way
  out, truncates `i64 -> i32` on the way in; `Unsigned32` zero-extends
  instead of sign-extends. This is a direct copy of the existing Bool
  widen/truncate code path with a different width and extend-kind, so it
  should be low-risk to implement once the existing Bool boundary code is
  located (`codegen/mod.rs`, per int-soundness-plan.md's own references to
  parameter-Kind binding there).
- Constructor (`signed32(n)`): reduce `i64 -> i32` via a plain LLVM
  `trunc` — likely literally reuses the existing `truncate32` builtin's
  codegen verbatim (same instruction; only the destination `Kind` label
  differs — `truncate32` labels its result `Kind::Int`, this labels it
  `Kind::Signed32`). Confirm the existing `truncateN` codegen helper's exact
  signature before assuming it's reusable as-is.
- Destructor (`from(x)`): sign-extend (`Signed32`) or zero-extend
  (`Unsigned32`) `i32 -> i64`, producing a plain `Kind::Int` result.

### Step order

1. **Parser**: none needed — no new grammar. `signed32(...)`/`unsigned32(...)`
   calls already parse as ordinary `Call` nodes; `Signed32`/`Unsigned32` are
   just names, same shape as `Int32`.
2. **Semantics**: register the two builtin names (a new `BuiltinKind`
   variant sitting alongside `IntBound`, since these are not `Int` subsets
   at all — `semantics/builtins.rs`); wire `kind.rs::set_kind` to the new
   `Kind::Signed32`/`Kind::Unsigned32`; fix `builtin_call_kind`
   (`elaborate.rs:178`) to return the wrapping Kind for these constructors,
   not `Kind::Int`; extend the `from` recognition to the new registry.
3. **Solver**:
   a. Spike the `Int ↔ BitVec` conversion formulas standalone against the
      `cvc5` crate first (see above) — resolve the medium-confidence
      unknowns before writing the real data structures.
   b. `WrappingInfo`/`WrappingPreds`, built by a `build_wrapping_preds`
      sibling to `build_distinct_preds` (`src/solver/mod.rs:132`).
   c. `set_sort` (`src/solver/sort.rs`) maps the two builtin names to their
      own `d_sort`.
   d. Generalize the `is_distinct_sort` cross-kind-union check
      (`sort.rs:322`) to also treat wrapping sorts as opaque/disjoint.
   e. Encode `+ - * neg` and comparisons for same-family operand pairs via
      `from_D`/`bv-op`/`mk_D` as above; leave the existing "sort mismatch →
      dummy value, rely on `Constrained(false)`" guard in place for mixed
      operands (e.g. adding a `Signed32` value to a raw `Int` without an
      explicit `from`/constructor call stays a domain error, exactly like
      today's `distinct` values in raw arithmetic).
   f. Constructor/destructor: no obligation needed for the constructor —
      unlike `distinct`'s basis obligation, wrapping construction is total
      (every `Int` maps to *some* bit pattern); `from` is likewise total.
4. **Codegen**: new `Kind` variants, `i32` register type, sext/zext ABI
   boundary crossings, arithmetic lowers to plain (non-checked) `i32`
   instructions, constructor/destructor as above.
5. **Tests/docs**: CLI e2e —
   - wraparound actually happens:
     `signed32(2147483647) + signed32(1) == signed32(-2147483648)`;
   - disjointness: passing a `Signed32` value where `Int` (or `Unsigned32`)
     is expected is a compile-time domain error;
   - signed vs. unsigned comparison on the same bit pattern:
     `unsigned32(4294967295) > unsigned32(0)` is `true`, but
     `signed32(-1) < signed32(0)` is also `true` for the *same* underlying
     bits, read the other way — a good documentation example for the
     gotchas appendix (§10).
   - design-decisions.md §13 gets a new "Wrapping fixed-width integers"
     subsection.

---

## Feature 2 — Quotient sets

### Prerequisite: `rem` / `quot` operators

**Status: DONE, 2026-07-05.** Implemented as sketched below, with two
adjustments made along the way (both confirmed with Doug):

1. **BigInt scope, narrower than this doc originally implied.** `+ - * /`
   all have a `cantor_bigint_*` runtime function so an unbounded, tagged
   `Int` operand still computes a correct (if BigInt-backed) answer.
   `rem`/`quot` don't get that treatment in this slice — no
   `cantor_bigint_rem`/`cantor_bigint_quot` exists yet, and rather than
   silently running plain-i64 Euclidean arithmetic on what might actually
   be a boxed BigInt pointer, an unbounded operand is a **compile-time**
   `Unsupported` error (not a runtime trap — `lk`/`rk` are already known
   statically at codegen time, so there's nothing to defer to runtime).
   Only a genuinely `Int64`-bounded operand (e.g. an `Int32`-domain
   function promoted by `int64_split`'s Step A) reaches the real Euclidean
   codegen. Adding the two runtime functions is a deferred follow-up.
2. **No set-position meaning.** Unlike `+ - * /`, `rem`/`quot` never had a
   "SetRem"/"SetQuot" dual planned — confirmed this means Set position is a
   hard `InvalidSetExpression` diagnostic, not silently falling through to
   some default.

**A real, pre-existing bug found and worked around (not fixed) while
writing the CLI tests**: a function's raw `Kind::Int64` result (post
`int64_split` promotion) flowing directly into a `Fail`-wire success
payload, or a tuple leaf, reaches the runtime *untagged*, but the
display/decode side (`format_tagged_int` in `src/main.rs`, and
`cantor_bigint_*` for the tagged-arithmetic path) assumes every `Kind::Int`
position is tagged. Reproduces identically with plain `/` (a
`Fail`-wrapped case prints a silently wrong value; a tuple-returning case
crashes with a misaligned-pointer panic in `src/runtime/bigint.rs`) — this
is **not** a rem/quot bug, it's a gap in the `Int64`→`Int` re-tagging
boundary for *any* promoted function's result used from a `Fail`-wrapped or
tuple-returning caller. All CLI tests below route around it by keeping
`main`'s return a bare `-> Int` (confirmed to tag correctly). Flagged to
Doug; not fixed here — out of scope for this slice, needs its own
investigation of where codegen assembles the `Fail`-wire struct /
tuple-into-buffer trampoline.

Needed unconditionally for the motivating example to even be *writable*
(`x -> x rem 5`), and independently useful — do this first regardless of
which feature lands first overall.

- New `BinOp::Rem`, `BinOp::Quot` (`src/ast.rs:164`, alongside the existing
  `Div`); `Token::Rem`, `Token::Quot` keywords, following the exact pattern
  `and`/`or`/`in` already use (`src/parser/lexer.rs:200-203` adds the
  string-to-token mapping, plus a `Display` arm at line ~92-95).
- Parser precedence: same tier as `*`/`/` (`src/parser/expr.rs:445-446`,
  `(15, 16, BinOp::Rem)` / `(15, 16, BinOp::Quot)`).
- **Solver, per fork 2 (Euclidean)**: this is actually the *easier* case,
  not a new encoding — cvc5's `Kind::IntsDivision`/`Kind::IntsModulus`
  (SMT-LIB `div`/`mod`) are already Euclidean, so `quot`/`rem` map onto them
  directly with no correction needed. Domain obligation: divisor ≠ 0,
  exactly `/`'s existing `binary_builtin_domain` row (`src/solver/mod.rs`
  per `project_builtin_domains` memory) — add `(Rem, 1) -> NonZeroInt` and
  `(Quot, 1) -> NonZeroInt` beside `(Div, 1)`.
- **`/`'s own truncating-vs-Euclidean mismatch is explicitly *not* this
  slice's problem to fix — confirmed with Doug 2026-07-05.** `/`'s current
  encoding (secretly Euclidean, documented as truncating) is a
  rapid-prototyping-era placeholder: `/` is intended to eventually produce
  `Rational`, not `Int`, at which point today's Int-truncating `/` is
  retired entirely and replaced by a dedicated, genuinely-truncating
  `tdiv`/`trem` pair (separate future work, low priority, not part of this
  plan). `quot`/`rem` are a wholly independent, Euclidean-by-design pair
  needed now for quotient-set canonicalizers — they don't need to agree
  with whatever `/` does today or will do once `Rational` lands. See
  design-decisions.md's "Arithmetic widening" section and §12 for the
  `Rational`/`tdiv`/`trem` forward-pointer.
- Codegen: LLVM `sdiv`/`srem` plus the standard sign-correction to convert
  hardware truncating division into Euclidean (`if rem < 0: rem += |d|;
  quot -= sign(d)`) — the same well-known transform used to implement
  Python's `%`/`//` over hardware division. Same `i64::MIN / -1` overflow
  corner as `/` needs the same existing guard.
- Tests/docs: `(-7) rem 5 == 3`, `(-7) quot 5 == -2`, divide-by-zero domain
  rejection for both, `/`'s own behavior (whichever way the note above
  resolves) covered by an explicit regression test either way.

### Quotient set formation: `L / canonicalizer`

**Status: DONE, 2026-07-05.** Landed close to this sketch, with the
"no codegen" and "no new solver sort" claims both holding up exactly as
predicted — confirmed by an explicit codegen regression test (a quotient
value flowing through an ordinary `Int`-typed function). Three real
surprises found only by implementing it, none anticipated by this doc:

1. **`SetQuotient`'s RHS had to become a bare `Symbol`, not a boxed
   `SemExpr`.** The original sketch assumed the canonicalizer reference
   could stay a normal sub-expression; in practice, elaborating it as an
   ordinary expression (Set or Value position) doesn't work at all, since
   `canon5` names a *function*, not a set or a runtime value — neither
   position's `Var` handling can resolve it (`name_defs` only holds
   `NameDef`s). Fixed by carrying the canonicalizer as a plain `Symbol` on
   `SemExprKind::SetQuotient`, resolved against `fn_env` only once it
   exists (solver time), never elaborated as an expression.
2. **A real, hard-won solver-design lesson: no persistent axiom.** The
   first working version registered the canonicalizer as an uninterpreted
   `canon : sort -> sort` and asserted `∀x. canon(x) == body(x)` onto
   *every* per-signature solver in the file (mirroring how `distinct`'s
   `mk`/`from` get re-registered fresh per solver instance). This
   **made cvc5 hang** on a file containing nothing but an unrelated
   function plus the quotient definition — injecting a quantified fact
   into every proof, even ones with nothing to do with the quotient set,
   revived the same quantifier/nonlinear-interaction risk this codebase
   already documents (the nl-cov note). Fixed by dropping the axiom
   entirely: `QuotientInfo` stores the canonicalizer's raw param+body, and
   `membership_constraint`'s `SetQuotient` arm calls `encode_comp_expr` to
   substitute the *specific* term being checked, no quantifier involved.
   The idempotence *proof* itself still needs a real quantifier — but that
   one only ever runs once, in its own isolated solver, in
   `validate_quotient_sets`, never injected into the general-purpose ones.
3. **`membership_constraint`'s signature needed widening across ~40 call
   sites** to reach the canonicalizer's body from inside membership
   checking (it didn't have `fn_env` and adding it broadly would have been
   far more invasive). Resolved with a `SolverPreds` wrapper — bundles the
   existing `DistinctPreds` with a new `QuotientPreds`, `Deref`s to the
   former — so call sites that only ever needed distinct-set info (the
   large majority, including every `set_sort` call) needed zero changes;
   only construction sites and direct field-reads needed touching.
4. **A pre-existing naming-convention checker false-positive**:
   `src/names.rs`'s uppercase-only rule for domain/range set expressions
   walked `BinOp`'s both children generically, rejecting `canon5` (correctly
   lowercase, a function name) as if it were a set name. Fixed with a
   `BinOp::Div`-specific exception, mirroring the doc's own pre-existing
   exception for `in`/`not in`'s RHS.

The whole feature is compile-time bookkeeping plus one new proof obligation.

- **Restrict the RHS to a bare named function reference** — reject any
  other expression shape (including any future lambda) with an explicit
  "canonicalizer must be a named function (lambdas not yet supported)"
  diagnostic at elaboration time. This is a shape check on `SetQuotient`'s
  already-existing RHS, not new grammar (the parser already accepts
  `SetQuotient(lhs, rhs)` for arbitrary set-position sub-expressions).
- **Validate the canonicalizer's declared signature**: `f : L -> L'` with
  `L' ⊆ L`, checked via the ordinary existing domain/range containment
  machinery — no new proof kind, this part *is* the standard graduated
  assert/assume-style obligation (only the idempotence claim below is the
  new "constitutive, no-assume" one).
- **The new obligation**: prove `∀x ∈ L. f(f(x)) == f(x)`. Per fork 3, an
  unproved result (timeout or genuine counterexample) is a **hard compile
  error**, framed the same way recursive-set well-foundedness is (§3) —
  there is no meaningful runtime fallback for "is this canonicalizer
  idempotent," since it's a claim about every element of a possibly
  infinite set, not a single value one could check at a call site.
  Encode as an ordinary quantified entailment — structurally the same shape
  as the existing sequence-membership `∀i. guard → elem∈X` goals, so it
  reuses the already-`mbqi`-enabled quantifier machinery with no new solver
  capability.
- **Runtime representation — the actual scope-reducer**: since no operators
  are derived yet, `L/f`'s Kind is simply `L`'s own Kind. An `IntMod5`
  value is stored exactly like an `Int` value already is (same `i64`, no
  tagging, no wrapper, no codegen changes at all). Membership is defined as
  the **fixed points of the canonicalizer**: `x ∈ L/f  ⟺  x ∈ L ∧ f(x) == x`.
  Passing an `IntMod5` value into a function typed over `Int` already works
  via the ordinary subset-domain-membership proof the compiler already does
  everywhere else — no quotient-specific call-boundary code needed.
- **Un-panic the existing placeholders** rather than build parallel new
  machinery:
  - `src/solver/sort.rs:369`'s `set_sort` gets a real
    `SemExprKind::SetQuotient` arm returning `L`'s own sort (quotient
    values live in the same sort as their canonical representative).
  - `membership_constraint` (`src/solver/membership.rs`) gets a case
    implementing the fixed-point definition above.
  - `src/solver/encode.rs:328`'s value-position `Err` arm is **unaffected**
    — `SetQuotient` still never legitimately reaches value position; that
    panic path stays exactly as correct as it is today.
- **Explicitly deferred, matching your framing exactly**: `deriving
  Arithmetic` / any operator auto-derivation on the quotient set; an inline
  lambda as the canonicalizer; the future `L = X * R` structural shortcut
  for `/`. All three get a one-line forward-pointer from design-decisions.md
  §12 once this lands.

### Step order

1. **Parser**: none — set-position `/` is already handled.
2. **Semantics**: reject a non-named-function RHS; validate
   `f : L -> L' ⊆ L`; record the quotient definition (likely a new
   `DefKind::Quotient` paralleling `DefKind::Distinct`, carrying the
   canonicalizer's `Symbol` — confirm the exact shape of `SemNameDef`/
   `NameDefs` supports this cleanly before committing to the variant name).
3. **Solver**: the one-time idempotence obligation, run once per quotient
   definition before the main per-function loop (parallel in spirit to how
   `validate_disjoint_unions`/`int64_split`'s pre-pass already run once over
   the whole file in `check_file`); the `set_sort`/`membership_constraint`
   arms above.
4. **Codegen**: none — confirm this with an explicit codegen-level
   regression test (a `IntMod5` value flowing through an ordinary
   `Int`-typed function compiles identically to a plain `Int` today),
   rather than silently assuming "no codegen work" and finding out
   otherwise later.
5. **Tests/docs**: CLI e2e for `IntMod5 = Int / canon5` with a genuine
   canonicalizer (`canon5(x) = x rem 5`... modulo whatever the `/`
   consistency decision above lands on) proving; `assert 7 in IntMod5`
   false, `assert canon5(7) in IntMod5` true; a non-idempotent function
   rejected with a witness; a non-named-function RHS rejected with the
   "lambdas not yet supported" diagnostic; an `IntMod5` value flowing into
   an ordinary `Int`-typed function with no special handling. design-
   decisions.md gets a new subsection (near `distinct`, §13) marking
   quotient sets DECIDED-for-this-slice, with the "no operators derived
   yet" caveat stated explicitly and a forward pointer to the deferred
   ideas already listed in §12.

---

## Suggested overall sequencing

**Status: all three steps DONE as of 2026-07-06** (`rem`/`quot` and quotient
sets 2026-07-05, `Signed32`/`Unsigned32` 2026-07-06) — this whole plan
document is now fully implemented. Sequencing actually used, matching the
reordering suggested below:

1. **`rem`/`quot` operators** — small, mechanical, useful standalone,
   unconditionally required before the quotient-set example can even be
   written.
2. **Quotient sets** — no codegen, no new solver sort; the fastest path to
   a working end-to-end demo of the headline `IntMod5` example, and the
   `/`-consistency question surfaces naturally as part of step 1 rather
   than being discovered mid-way through step 2.
3. **`Signed32`/`Unsigned32`** — the larger, more solver-novel piece (new
   sort family, the `Int ↔ BitVec` conversion spike, cross-kind union
   generalization). Nothing about it was blocked by 1 or 2 landing first;
   it was sequenced last purely because it was the biggest chunk of new
   solver ground, not because anything depended on it.

Remaining follow-ups explicitly deferred out of this plan (not tracked
further here): `cantor_bigint_rem`/`cantor_bigint_quot` runtime functions
(§ rem/quot scope note), the pre-existing `Int64`→`Int` re-tagging gap for
`Fail`-wire/tuple payloads (see `project_int64_retag_gap` memory — a
pre-existing bug, not introduced by this plan), additional wrapping widths
(`Signed8/16/64`, …), and division/remainder on wrapping sorts.
