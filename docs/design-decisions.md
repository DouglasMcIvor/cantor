# Cantor — Design Decisions

Working reference for implementation. States conclusions only, not rationale —
treat everything marked DECIDED as settled; do not re-litigate without new
information. Items marked OPEN are genuinely undecided.

Tagline: "Types without Types" / "Who needs types anyway?"

## 1. Core concept

- Set-theoretic foundation instead of type theory. Function safety comes from
  proving domain/range containment, not from a type system.
- Mostly pure functional, Haskell-like surface syntax, but function bodies
  support local **mutable** variables (see §5). Purity = no effects escape
  the function except via the explicit mechanisms in §4.
- Compiler must prove function composition respects domains/ranges (e.g.
  divide's domain excludes zero). Failure to prove → compile error with a
  diagnostic and (where possible) suggested constraints that would close the
  proof gap, generated from the solver's unsat core.

## 2. Sets — static vs generative

- **Static sets**: fully materialised at runtime, finite, iterable, has a
  computable cardinality (`size(S)`, never `len`, to avoid implying order).
- **Generative sets**: defined by comprehension/recursion, exist only as
  symbolic objects for compile-time reasoning. Never appear in runtime value
  positions (locals, State) — only in compile-time constraint positions
  (domains/ranges).
- **Equality**: structural. Sets with equal elements are identical ("Bosonic
  statistics") — no identity/reference equality for sets.
- Equality of sets defined by arbitrary predicates: undecidable in general →
  same policy as everything else: solver attempts proof, falls through to
  assert/assume on failure.
- **`take n from S`**: materialises a generative set into a static set of
  size ≤ n. Implementation is free to choose the "cheapest to find" n
  elements (no natural ordering). Deterministic for a given binding within a
  single program run (referential transparency preserved); may vary across
  separate runs/compilations or across implementations.
- Eager evaluation at runtime. Laziness is confined to generative sets only
  — there is no general lazy evaluation model.

## 3. Recursion

### Recursive sets
- Require a well-foundedness proof (the recursion is constitutive of the
  set's denotation — an ill-founded definition doesn't denote a set at all).
- Three-tier staged approach:
  1. **Structural recursion** (recursive occurrence strictly under a
     constructor, e.g. `BinStr = {ε} ∪ {0++s | s ∈ BinStr} ∪ {1++s | s ∈ BinStr}`)
     — automatically recognised, zero solver cost, compiler confirms this
     explicitly to the developer.
  2. **`decreasing by <measure>`** — explicit annotation escape hatch for
     non-structural cases. DEFERRED past v0 (ship as "not implemented yet"
     error initially).
  3. **Automatic measure inference** — compiler searches for a decreasing
     measure itself. DEFERRED further; layers on top of (2) without
     invalidating hand-written annotations.
- v0 prototype: only tier 1 (structural) need work. Non-structural recursive
  sets are a hard error: "cannot verify well-foundedness — not yet
  implemented."

### Recursive functions
- **No well-foundedness/termination proof required to compile.** Only
  domain/range containment is checked (recursive call site treated like any
  other call, using the function's own signature as induction hypothesis).
  Non-terminating functions are valid, coherent partial functions — same
  stance as virtually every mainstream language.
- Termination checking is a separate, deferred, *optional* feature:
  three-tier outcome model —
  - proven-terminating → silent
  - proven-non-terminating → **always** a hard error (not gated by -Wall)
  - unproven either way → warning by default; `-Wall`-style strictness
    escalates to error, forcing an explicit `decreasing by <measure>`
    annotation (same mechanism as recursive sets, conceptually distinct
    check).
- v0 prototype: no termination checking at all (permanently in the
  "unproven, no warning" state). Include a test case that is
  domain/range-valid but possibly non-terminating, to confirm the compiler
  accepts it without attempting termination analysis.

## 4. Error handling — three classes

1. **Class 1 — domain/range violations ("normal" errors).**
   - Implicit `Option` wrapping: if the compiler can't prove a function's
     output stays in range (or input in domain), the return type is
     automatically wrapped in Option.
   - Short-circuit (monadic, not exception-like) semantics, explicit `?`
     marking at each fallible call site for local visibility.
   - `assert` = runtime-checked narrowing (also aids downstream proofs).
     `assume` = same narrowing, no runtime check, for performance — "live
     dangerously."
   - Runtime membership testing for predicate-defined sets evaluates the
     predicate unless the compiler can prove/partially-prove it away.
     Developer intuition: `assert` can be expensive for complex predicates.
   - A single function body may freely mix Class 1 and Class 2 constructs —
     no purity-of-class restriction.

2. **Class 2 — exceptional/environmental failures (no recovery path).**
   - Network timeouts, disk full, etc. — failures that are NOT a domain/range
     gap, but the outside world misbehaving in a way no proof could predict.
   - A single non-network-style external call (e.g. one HTTP attempt) is
     just an ordinary Class 1 function returning a sum type, e.g.
     `httpCall : Request → Either<Response, HTTPError>`. Retry/backoff logic
     (e.g. `fetchWithRetry`) is ordinary pure Class 1 code looping over that
     sum type. **Class 2 only begins at the explicit point a developer
     writes `raise`** to convert "I'm out of options" into a terminal
     effect — e.g. `fetchPrice` raises `ServiceUnavailable` only once
     `fetchWithRetry` is exhausted.
   - `raise` effects are **fully inferred** via transitive closure over the
     call graph — no developer declaration required at intermediate call
     sites (no decision point exists for the developer once something is
     unrecoverable and uncatchable, so requiring annotation would be
     busywork). Optional explicit `raises X` annotation permitted purely for
     documentation, checked against inference rather than required.
   - **"One catch"**: `raises` effects can ONLY be caught/consumed at the
     event loop boundary (`(Event, State) → (Output, State)`), structurally
     enforced, not conventional. Surfaces as a small closed Output set, e.g.
     `Success | SystemError | UserError`.
   - A Class 2 failure during event processing **rolls back State** to its
     value immediately prior to the event (atomic event processing).
   - Retry/backoff at the "given up entirely" level (vs the in-library
     backoff loop) is modelled as explicit Event/State transitions (e.g. a
     synthetic retry event), not as a local catch-and-retry construct.
   - **No `assume`-style escape hatch for Class 2.** Deliberately harder to
     reach for than Class 1 — there's nothing to "prove away" for an
     environmental failure.

3. **Class 3 — language/runtime-level failures.**
   - Syntax errors, stack overflow, OOM, compiler-internal invariant
     violations.
   - Entirely outside Cantor's value/effect universe — not representable as
     a value, not catchable by any in-language mechanism. Surfaces as a
     runtime crash/diagnostic only, never as something a Cantor program can
     pattern-match on. (Prevents the Python-style problem of an exception
     handler accidentally catching a syntax error.)

### Write-only effects (`emits`)
- Logging/metrics/debug output generalised as **write-only emitted
  effects**, structurally parallel to `raises` but non-terminating.
- Fully inferred (same justification as `raises`).
- No in-language read-back mechanism anywhere — enforced by absence of any
  consuming construct, not by a runtime restriction.
- Test frameworks get a privileged exception to observe emitted
  streams — they act as a stand-in for the event loop boundary, not via a
  general language feature.
- Likely **multiple typed channels** (Log, Metric, Trace, ...) rather than
  one undifferentiated stream. (OPEN: confirm channel set and emit syntax.)
- `emits` data does not accumulate in State; flushing/buffering is an
  implementation detail of whatever sits at the event loop, not part of
  Cantor's pure semantics.
- DEFERRED (future): emit handlers themselves written in Cantor. Opens
  questions about handler failure semantics — explicitly out of scope for
  now.

## 5. Mutability

- Local mutable variables ARE allowed within function bodies (deliberate
  "yes and" alongside fold/map/pure-functional style) — purity is preserved
  because mutation never escapes function scope, not because locals are
  immutable.
- **Output parameters are 100% banned.** Locals are fully local, full stop.
- Aliasing/references to a local within the same function scope: leaning
  toward banning for simplicity (OPEN — not fully confirmed, but treat as
  default-banned unless revisited).
- Mutable locals cannot hold a lazy/partially-evaluated generative set
  (consistent with the static/generative confinement rule in §2).
- A mutable local has a "trajectory" through some set S over the function
  body; compiler does loop-invariant-style inference, falling back to
  assert/assume when it can't determine the invariant automatically.
- Syntax: needs a visible mutability marker (tentatively `mut` on first
  introduction, Rust-style) so mutation is visually distinct from
  Haskell-style immutable `let`-binding, which `name = expr` would otherwise
  resemble. (OPEN — not fully finalized, but treat `mut` as the working
  default.)

## 6. IO / Event loop

- Implicit event loop: program defined as `(Event, State) → (Output, State)`.
  Immediate-mode output is the default model.
- State must be **fully static** — no generative/partially-evaluated sets,
  no pending/buffered `emits` data.
- Compiler/runtime needs structural-sharing/diffing so unchanged state isn't
  recreated from scratch (persistent data structures, not naive rebuild).
- OPEN: exact type of Event (built-in union vs user-definable).
- OPEN: concurrency/async event handling model (strictly queued vs other).

## 7. Compilation model

- **Unit of compilation = the library** (not file, not whole-program). Allows
  cross-file inference within a library; bounds inference scope across a
  whole program.
- Libraries expose an **interface**: function signatures with domain, range,
  inferred `raises` set, inferred `emits` set — all are part of the public,
  black-boxed contract. Implementations are hidden from external callers.
- **Function overloading over disjoint sub-domains** is supported, even when
  multiple declared signatures share one underlying implementation.
  - Compiler verifies the shared implementation independently satisfies
    each declared overload's domain/range (reuses ordinary domain/range
    checker, no new machinery).
  - Overload resolution at call sites is itself a proof obligation
    (static-proof-first, runtime-tag-check fallback, same pattern as
    everywhere else).
  - **Overlapping overload domains are forbidden — disjointness is
    required, checked at compile time, overlap is a compile error.** (Not
    resolved by most-specific-wins or similar — avoids developer confusion
    over resolution rules.)
  - Automatic domain-partition inference (compiler infers a good overload
    split rather than requiring hand-declaration) is an explicitly deferred
    future feature.
- OPEN: how a library's interface is declared syntactically (separate
  interface file vs inline visibility annotations).
- OPEN (acknowledged, out of scope for prototype): library
  interface versioning/compatibility story.

## 8. Solver-dependent compilation (accepted trade-off)

- Where a question is undecidable in general (solver timeout, predicate
  equality, etc.): "unable to prove" → falls through to requiring an
  explicit `assert`/`assume` from the developer. This is the single
  unifying policy response to undecidability throughout the language.
- Accepted: a program that compiles under one implementation's solver may
  not compile under a weaker one. Acceptable trade-off, especially as only
  one implementation is currently planned.
- DEFERRED (nice-to-have, not urgent): solver-capability versioning, so a
  program could declare "requires solver capability level N."

## 9. Toolchain

- **Constraint solver: cvc5** (chosen over Z3). Reasons: native theory of
  finite sets and relations (Z3 has no native set theory — would require
  hand-built encodings), dedicated QF_FS logic fragment with cardinality
  constraints, active research specifically on set comprehensions and
  bounded quantifiers, well-documented unsat-core extraction (drives the
  "suggested constraints" diagnostic feature), and a "pythonic" API
  deliberately designed to mirror Z3's API shape if ever needed.
  - Rust integration: **official `cvc5-rs` crate** (safe high-level API)
    + `cvc5-sys` (FFI), maintained by the cvc5 project itself, not a
    third party. Has a `static` feature to auto-build cvc5 from a git
    submodule — no separately-installed system cvc5 required.
- **Implementation language: Rust.** Reasons: mature LLVM bindings
  (Inkwell), strong representation in training data for compiler/LLVM work
  specifically, philosophical alignment between Rust's "catch errors at
  compile time / make illegal states unrepresentable" ethos and Cantor's
  own goals, genuine professional learning value, reasonable FFI story for
  wrapping cvc5.
- **Compiler backend: LLVM.**
- **Compiler from day one** — not interpreter-first. Cantor should feel
  statically-typed/compiled from the start (Haskell/Rust/C++ register, not
  Python/JS).
- **Parser: hand-written recursive descent.** Reasons: maximal control over
  diagnostic quality (a first-class design goal, not an afterthought),
  handles Cantor's context-sensitive grammar wrinkles (comprehensions,
  domain/range annotations, assert/assume/decreasing-by family, overload
  sets) more gracefully than a generator, avoids adding a third unfamiliar
  tool/DSL on top of Rust+LLVM+cvc5 already being new territory, matches
  prior positive experience. Precedence climbing/Pratt parsing for
  expressions — pattern to be worked out collaboratively when reached, not
  designed in the abstract ahead of time.
  - Rejected alternatives: `pest` (separate grammar file reintroduces the
    indirection being avoided); `nom`/`chumsky` combinators (reasonable
    middle ground, but unnecessary given recursive descent is the
    preferred and already-familiar approach) — may revisit for a specific
    painful sub-grammar (e.g. just expression precedence) if needed later.

## 10. Syntax — settled so far

### Documentation architecture
- **Two-tier docs, divergent in content (not just compression):**
  - Human intro: motivation, mental models, worked examples, "why."
  - LLM intro: terse grammar/operator reference, decision-tree-style
    summary of the error-class model, explicit "looks like X but isn't"
    section (the gotcha list from below), assumes deep background
    knowledge, skips motivation/history.
- **Rare, compile-time-detectable gotchas live in an indexed appendix**, not
  the standing intro — keeps LLM context usage low. Compiler diagnostics
  point directly into the relevant appendix entry.
- Appendix mechanism: **a folder of markdown files, one per error code**
  (e.g. `errors/E0231-overload-domain-overlap.md`). Deliberately low-tech.
- **Error code slugs are permanently stable once assigned** (never
  renumbered/renamed, same discipline as Rust's `E0502`-style codes).

### Known gotchas to document explicitly (non-exhaustive, grows over time)
- `name = expr` for a *new* mutable binding needs a visible marker
  (tentatively `mut`) — bare `=` would otherwise read as Haskell-style
  immutable `let`, which is NOT what it means in Cantor.
- `==` is always **structural** set equality, never reference/identity
  equality — relevant since other languages in many devs'/LLMs' background
  knowledge default to reference equality for compound values.

### Set operators (Unicode primary, ASCII equivalent required for all)
| Concept | Unicode | ASCII |
|---|---|---|
| Union | ∪ | `\|` |
| Intersection | ∩ | `&` |
| Symmetric difference | — | `^` (matches XOR intuition deliberately — symmetric difference IS set-XOR) |
| Set difference | ∖ | `-` (NOT `\` — avoid escape-char/path-separator overload) |
| Membership | ∈ | `in` |
| Not member | ∉ | `not in` |
| Subset / proper subset | ⊆ / ⊂ | `<=` / `<` |
| Superset / proper superset | ⊇ / ⊃ | `>=` / `>` |
| Cardinality | \|S\| (math convention) | `size(S)` as the actual syntax — avoids visual clash with `\|` as union, avoids `len` because it would wrongly imply an ordering |

### Comprehensions
- Mirrors Python set-comprehension syntax: `{ expr for x in S if pred(x) }`
  — isomorphic to math notation `{ expr | x ∈ S, pred(x) }`, no semantic
  departure from the original mathematical framing.
- **Multi-binder comprehensions supported**:
  `{x+y for x in A for y in B}` desugars to a single-binder comprehension
  over the Cartesian product `A × B` — pure sugar, no new semantic
  machinery needed beyond what's already specified.
- Comprehension result range: inferred first, falls through to the
  standard assert/assume pattern when the solver can't determine it
  automatically — confirms the general undecidability policy (§8) extends
  to comprehensions without needing a new mechanism.

## 11. Open questions for next session

Syntax (next logical unit of work — these were flagged as wanting to be
designed together rather than piecemeal):
- Function definition syntax (domain/range annotation form)
- `assert` / `assume` / `decreasing by` statement syntax
- `raise` / `emits` statement syntax (incl. whether `emits` is one channel
  or several, and what the channel set is)
- Module/library interface declaration syntax (separate file vs inline)
- Finalize the mutability marker (`mut` is the working default, not fully
  locked in)
- Aliasing/references to locals within the same function scope — leaning
  banned, not fully confirmed

Other open items (lower priority, not blocking):
- Event type definition (built-in union vs user-definable)
- Concurrency/async event handling model
- Library interface versioning story (acknowledged out of scope for now)
- Solver-capability versioning (deferred, nice-to-have)

## 12. Explicitly deferred future features (not in scope, do not implement
    speculatively)

- `decreasing by <measure>` annotation for recursive sets (tier 2) and
  automatic measure inference (tier 3)
- Termination checking for recursive functions (three-tier
  proven/disproven/unproven + `-Wall` escalation)
- Automatic domain-partition inference for overload sets
- Emit handlers written in Cantor itself
- Solver-capability versioning

## 13. Prototype approach

- Build via a **unit-test suite for the compiler** rather than a polished
  first syntax — syntax is expected to be reworked multiple times before
  settling, so tests should target semantic behavior/diagnostics over exact
  surface syntax where possible, to reduce churn cost across rewrites.
- v0 feature scope per the staged decisions above: structural-recursion-only
  for recursive sets, no termination checking for recursive functions, core
  three-class error model, static sets + basic comprehensions, library-level
  compilation with disjoint overloads.
