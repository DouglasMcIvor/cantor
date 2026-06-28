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

## 2a. Naming convention — uppercase vs lowercase (DECIDED)

Cantor enforces a single rule: **uppercase-initial names are guaranteed
compile-time; lowercase-initial names may be compile-time or runtime.**

| Name style | Guaranteed | Allowed positions |
|---|---|---|
| `Uppercase` | compile-time only | type signatures, set definitions, `in`/`not in` operands |
| `lowercase` | either (compiler decides) | everywhere |

**Consequences:**

- **Type signatures must use uppercase names.** `f : Int -> Nat | Fail`
  is legal; `f : Int -> collected_primes` is a compile error — not because
  `collected_primes` is checked for staticness, but because a lowercase
  name is syntactically invalid in that position. The constraint on
  signatures is therefore enforced by the naming rule alone.

- **User-defined named sets must be uppercase.** `HTTPError = {400, 503}`
  is a named-set definition; `httpError = {400, 503}` is a local variable
  binding that happens to hold a set literal. The resolver uses the
  first-letter case to distinguish them — no keyword or annotation needed.

- **Constants are lowercase** even though the compiler may evaluate them
  at compile time. `pi : Nat / pi = 314` — `pi` is a value (auto-constexpr
  if it qualifies; see §12 zero-arg functions), not a set, so it stays
  lowercase. The developer makes no promise about when it is evaluated;
  the compiler chooses as an optimisation.

- **Runtime sets are lowercase.** `collected_primes` computed by a sieve
  at runtime is a perfectly valid `assert x in collected_primes` operand
  — it just cannot appear in a `:` type signature.

- **`in`/`not in` operands accept either case.** `assert x in Nat` (static
  set) and `assert x in collected_primes` (runtime set) are both legal;
  the resolver checks the RHS against the known namespace rather than
  relying on case alone.

This ties directly to the `emits`/auto-constexpr rule in §12: a name
being lowercase says nothing about *when* it is evaluated — that is an
implementation detail the developer should not rely on.

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
   - **`Fail` as built-in set, explicit `| Fail` in range**: a function
     that can fail at runtime declares this in its range: `f : Int -> Nat | Fail`.
     `Fail` is a named built-in singleton set; it is the tag, not a generic
     `Option`/`Result` wrapper.
   - **`fail` literal and `fail expr`**: `fail` produces a bare failure; `fail
     400` constructs a tagged failure with payload 400. Fallible functions return
     a `{i1, i64}` struct at the LLVM level: flag i1=1 means failure, flag i1=0
     means success. Success and failure are always distinguishable regardless of
     the numeric value — `success 400` and `fail 400` are distinct because the
     flag bit differs.
   - **Error-union operator `!!`** — `Success !! ErrorSet` desugars at parse
     time to `Success | (Fail * ErrorSet)`. Example: `fetch : Int -> Int !!
     HTTPError`. Semantically equivalent to `Success | (Fail * HTTPError)`.
     The `?` operator on any fallible callee propagates the failure struct
     unchanged; no decoding is needed since the error code is the payload field.
   - **Short-circuit (monadic) semantics**, explicit postfix `?` at each
     fallible call site for local visibility: `f(x)?` propagates the failure
     struct from the callee up to the caller unchanged.
     The caller must also declare `Fail` or `!!` in its range.
     Using `?` in an infallible function (range without `Fail` or `!!`) is a
     compile error.
   - **`assert … else fail expr`** — when the predicate is false, returns
     `{i1=1, i64=expr}` (a typed failure struct). Useful inside `!!` functions
     to return a specific error code.
   - **`assert … else return expr`** — when the predicate is false, returns
     `expr` directly (early exit with a success value).
   - Three narrowing statements (not function calls); syntax and semantics
     detailed in §10:
     - `require` — static-only proof obligation: must be provable at compile
       time or it is a hard compile error. Equivalent to C++ `static_assert`.
       No runtime code emitted.
     - `assert` — graduated: if provable → elide + add fact; if disprovable
       → compile error; if unknown → emit a runtime membership check that
       returns a Class 1 error on failure (requires monadic `?` propagation).
     - `assume` — no check ever; compiler accepts the claim as a fact. Unsound
       if wrong — "live dangerously."
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
- **Syntax (DECIDED)**: `mut name: Set = expr` introduces a mutable variable;
  the `Set` annotation is the declared invariant — the set every reassignment
  must stay in and that is assumed true at the top of each loop iteration.
  `name := expr` *re*assigns it. Plain `name = expr` inside a `{ }` body is
  an immutable local binding — using `:=` on such a name is a compile error.
  Compound mutation operators follow the same two-character form: `+=`, `-=`, etc.

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
- **Module/file structure (DECIDED)**: one file = one module. Module name
  mirrors the file path relative to the library root, with `/` replaced
  by `::`. Example: `src/math/integers.cantor` → module `math::integers`.
  `::` is the module path separator for qualified names
  (`math::integers::safe_div`). This keeps file structure and module
  structure in strict 1-to-1 correspondence — no flexible re-exports that
  diverge the two. Consequence: `.` is freed from namespace duty and
  available for function composition (see §11).
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
- `Bool` is **not** an integer and cannot be used in arithmetic or numeric
  comparisons. `true` is not `1`; `false` is not `0`. No implicit coercion
  exists. This bites developers coming from C, Python, or JavaScript.
- `:=` is *re*assignment only — using `:=` as a first binding is a compile
  error. Developers from Pascal/Delphi know `:=` as the general assignment
  operator (used for all assignment including first binding); in Cantor first
  binding is always `mut name = expr`.
- `a < b < c` is a domain violation, not Python-style chained comparison.
  It parses as `(a < b) < c`, where `a < b : Bool` and `Bool` is disjoint
  from the domain of `<`. The intended idiom is `a < b and b < c`.

### Set operators (Unicode primary, ASCII equivalent required for all)
| Concept | Unicode | ASCII |
|---|---|---|
| Union | ∪ | `\|` |
| Disjoint union | — | `+` (operands must be proved disjoint; statically checked) |
| Intersection | ∩ | `&` |
| Symmetric difference | — | `^` (matches XOR intuition deliberately — symmetric difference IS set-XOR) |
| Set difference | ∖ | `-` (NOT `\` — avoid escape-char/path-separator overload) |
| Membership | ∈ | `in` |
| Not member | ∉ | `not in` |
| Subset / proper subset | ⊆ / ⊂ | `<=` / `<` |
| Superset / proper superset | ⊇ / ⊃ | `>=` / `>` |
| Cardinality | \|S\| (math convention) | `size(S)` as the actual syntax — avoids visual clash with `\|` as union, avoids `len` because it would wrongly imply an ordering |

### Product set values (tuples) (DECIDED)

Anonymous product values are fully supported. The `*` operator in a signature
denotes a product set (same as Cartesian product); at the value level, `(e1, e2)`
is a tuple literal and `t.0`, `t.1` are positional projections.

```
fst : Int * Int -> Int
fst(t) = t.0

swap : Int * Int -> Int * Int
swap(t) = (t.1, t.0)

-- Nat constraints propagate through projections
sum_pair : Nat * Nat -> Nat
sum_pair(t) = t.0 + t.1

-- main may return a tuple; cantor run prints it as (a, b)
main : -> Int * Int
main() = swap((3, 9))   -- main() = (9, 3)
```

**Arity disambiguation rule (DECIDED)**: given `f : <domain> -> R` with n declared
parameters, let `parts = flatten_product(domain)`.
- `parts.len() == n` → n separate scalar parameters (classic behaviour, unchanged).
- `n == 1` and `parts.len() > 1` → one tuple parameter whose set is the whole domain.
- Otherwise → arity error.

So `add(x, y)` with `Int * Int -> Int` continues to mean two scalars; only
`add(t)` with one param becomes a tuple param.

**Runtime representation**: by-value LLVM structs (`struct_type`,
`build_insert_value`, `build_extract_value`). No heap allocation.

**SMT encoding**: tuple params are always decomposed into leaf scalar constants
assembled with `mk_tuple`. A symbolic `mk_const` with a tuple sort is never
created — cvc5 rejects such terms in arithmetic contexts even when the element sort
is integer. Projection uses `child(i + 1)` on `APPLY_CONSTRUCTOR` terms rather
than `TupleProject` for the same reason. Logic must be `"ALL"` (replaces
`"QF_UFNIA"`) to enable datatype/tuple support.

**`main` trampoline**: when `main` returns a tuple, codegen emits
`cantor_main_into(*mut i64)` which stores each leaf into a caller buffer, avoiding
fragile struct-return FFI.

### Kleene-star sets and vectors (`X*`) (solver complete; codegen complete for Int*/Bool*)

`X*` is a postfix set operator that denotes the set of all finite sequences of elements
drawn from `X`.  It is the standard Kleene closure: `{} | X | X×X | X×X×X | …`.

**Syntax**: postfix `*` in any set-expression position.  The `*` is disambiguated from
infix Cartesian-product `*` by looking at the following token: if no expression follows
(e.g. `->`, `)`, newline), the `*` is a Kleene star.

```
-- Range: the function returns a variable-length sequence of Nat values
f : -> Nat*
f() = [1, 2, 3]   -- array literal coerced to Arrow Int64Array at function return

-- Domain and range (identity pass-through)
g : (Int - {0})* -> Int*
g(xs) = xs

-- Length of a vector is a Nat (built-in `len`)
h : Nat* -> Nat
h(xs) = len(xs)

-- Block-body binding: coerces the literal to a vector at the binding site
block_coerce : -> Nat
block_coerce() {
    xs : Nat* = [10, 20, 30]
    return len(xs)
}

-- Runtime indexing: xs[i] where i is a runtime value (Nat)
get_second : Nat* -> Nat
get_second(xs) {
    i : Nat = 1
    return xs[i]
}

-- Concatenation: xs ++ ys produces a new vector (O(n+m), purely functional)
concat_len : -> Nat
concat_len() {
    xs : Nat* = [1, 2]
    ys : Nat* = [3, 4]
    zs : Nat* = xs ++ ys
    return len(zs)        -- 4
}
```

**AST**: `ExprKind::KleeneStar(Box<Expr>)`.  The inner expression is the element set.
Runtime indexing uses `ExprKind::Index { base, index }`.  Concatenation uses
`BinOp::Concat` (parsed from `++`, same precedence as `+`).

**Runtime kind**: `Kind::Vector(Box<Kind>)` — variable-length sequence.  Wire type: `i64`
(pointer-as-i64) to a heap-allocated Apache Arrow array.

**Codegen support** (COMPLETE for `Int*` and `Bool*`):

*Representation*: `Kind::Vector(Kind::Int)` uses Apache Arrow `Int64Array`;
`Kind::Vector(Kind::Bool)` uses Apache Arrow `BooleanArray`.  Both are heap-allocated
via `Box::into_raw` and carried across function calls as `i64` pointer values, matching
the compiler's uniform calling convention.

*Construction — array literals*: An array literal `[1, 2, 3]` parses to
`ExprKind::Tuple`.  Coercion to a vector happens at two sites:
- **Function-return boundary**: when the declared range is `X*`, `coerce_vector_return`
  calls `compile_tuple_as_vector` before the LLVM `ret`.
- **Block-body binding site**: `xs : Nat* = [1, 2, 3]` in a block body is handled by
  `coerce_to_vector_if_needed` in `compile_stmts`, which checks the constraint and
  coerces the tuple to a vector before binding the name.

```
-- Emitted LLVM (schematic) for make_vec() = [1, 2, 3] with range Nat*
builder = cantor_vec_builder_new_i64()
cantor_vec_builder_push_i64(builder, 1)
cantor_vec_builder_push_i64(builder, 2)
cantor_vec_builder_push_i64(builder, 3)
return cantor_vec_builder_finish_i64(builder)
```

The builder produces an Arrow array in O(n) time.

*Pass-through*: Vector parameters arrive as `i64` pointers and are carried in the local
environment with `Kind::Vector(K)`, so `identity_nat(xs) = xs` compiles to a single
register move with no copies.

*`len(xs)` built-in*: dispatches to `cantor_vec_len_i64` or `cantor_vec_len_bool`
depending on the element kind.

*`xs[i]` runtime indexing*: `ExprKind::Index { base, index }` dispatches to
`cantor_vec_get_i64` or `cantor_vec_get_bool`.  No bounds check is emitted (the SMT
solver proves the index is in range where possible; otherwise the check is deferred
to runtime via `assert`/`assume`).  Compile-time literal indices (non-negative integer
literals) still desugar to `ExprKind::Proj` for tuple access.

*`xs ++ ys` concatenation*: `BinOp::Concat` dispatches to `cantor_vec_concat_i64` or
`cantor_vec_concat_bool`, both of which copy all elements into a new Arrow array (O(n+m)).
The old arrays are unmodified (purely functional).  If one or both operands are array
literals (parsed as `ExprKind::Tuple`), they are coerced to vectors first.

*Functional push*: `cantor_vec_push_i64(vec, val) -> new_vec` creates a new Arrow array
with the element appended (old array is preserved).  This is O(n) per call — acceptable
for Cantor's functional style.  Cantor source code cannot yet call push directly; it is
an internal runtime primitive used by the builder path.

*Block body and early `return`*: Functions with explicit `return` statements compile
correctly.  The solver currently reports such functions as Unknown (the SMT block encoder
does not yet support early `return` — it is aware of the limitation and will not produce
false proofs).

*Nested vectors (`Nat**` = `(Nat*)*`)* (COMPLETE):

`Nat**` is backed by Apache Arrow `ListArray` where the child type is `Int64`.
The outer vector is a `CantorListVecI64` (wrapping a `ListArray`); each inner
element is a `CantorVecI64` (wrapping an `Int64Array` slice of the child buffer).

```
-- Build, index, and concat at two levels
make : -> Nat**;   make() = [[1, 2, 3], [4, 5]]
f    : Nat** -> Nat;  f(xss) = len(xss)         -- 2
g    : Nat** -> Nat;  g(xss) { i:Nat=1; j:Nat=2; return xss[i][j] }  -- 5
```

- `xs[i]` where `xs : Nat**` calls `cantor_list_vec_get_i64(xs, i)`, which
  returns a new `CantorVecI64` wrapping an O(1) Arc-sliced view into the child buffer.
- `++` calls `cantor_list_vec_concat_i64(a, b)` — O(total child elements).
- `len(xss)` calls `cantor_list_vec_len_i64(xss)` — the outer list length.
- Block-body coercion (`xss : Nat** = [[1,2],[3,4]]`) works by recursively
  coercing each inner tuple literal to a `CantorVecI64`, then pushing those
  pointers into a `ListBuilder<Int64Builder>`.
- `Bool**` is symmetric, backed by `ListArray` with `Boolean` child.

*Struct vectors (`(Nat * Nat)*` = vector of tuples)* (COMPLETE):

`(A * B)*` is backed by a `CantorStructVec` holding one Apache Arrow `Int64Array`
per field — the same columnar layout that Arrow `StructArray` uses internally.
Bool fields are widened to `0/1 i64` at push time and truncated back to `i1` on
get. The field count is passed to `cantor_struct_vec_builder_new(n_fields)` at
runtime and stored in the struct, so the ABI is fully generic across any tuple shape.

```
-- Build, index, and project fields
make : -> (Nat * Nat)*;  make() = [(1, 10), (2, 20), (3, 30)]
f    : (Nat * Nat)* -> Nat;  f(ps) = len(ps)           -- 3
g    : -> Nat;              g() = make()[0].0           -- 1
h    : -> Nat;              h() = make()[2].1           -- 30
```

- `xs[n]` (literal n) and `xs.n` (dot notation) are syntactically equivalent —
  both produce `ExprKind::Proj`. On a struct-vector base (`(A * B)*`) `compile_proj`
  routes to `compile_struct_vec_index`, calling `cantor_struct_vec_get_field(xs, n, field)`
  for each field and assembling an LLVM struct result.
- `xs[i]` (non-literal i) produces `ExprKind::Index`, handled the same way.
- `++` calls `cantor_struct_vec_concat(a, b)` — O(total rows × fields).
- `len(ps)` calls `cantor_struct_vec_len(ps)` — length of any column.
- Block-body coercion (`ps : (Nat * Nat)* = [(1,2),(3,4)]`) uses
  `cantor_struct_vec_builder_push_field(builder, field_idx, value)` once per field
  per row.
- The solver currently returns Unknown for any function involving struct-vec
  indexing (projection on a sequence-sorted term is not yet SMT-encoded).
  TODO: add `SeqNth + ApplySelector` encoding for struct-vec index proofs.

*TODO — deferred*:
- Vectors of unions `(Nat | Bool)*` — DenseUnionArray (pending runtime union value design)

**Solver support** (COMPLETE):

*CVC5 sort*: `X*` is encoded as the CVC5 sequence sort `(Seq elem)` where `elem` is
`set_sort(X)`.  This uses the cvc5 theory of sequences (logic `ALL`).

*Membership encoding* (`t ∈ X*`): Two cases depending on the sort of `t`:
- **Sequence-sorted term** (variable-length `X*` parameter):
  ```
  ∀ i. 0 ≤ i < len(t)  →  nth(t, i) ∈ X
  ```
  This is a universally-quantified formula.  cvc5 is configured with
  `mbqi=true` (model-based quantifier instantiation) so it can also produce
  counterexamples for the negated-universal direction (finding a witness element
  outside `X`).  If cvc5 returns `unknown` for a quantified goal it surfaces
  honestly as `Unknown`; a silent pass is never produced.
- **Tuple-sorted term** (fixed-length concrete body like `[1, 2, 3]`):
  Each element is checked against `X` individually by child projection — no
  quantifier needed.

*`len` built-in*: `len(xs)` encodes to `seq.len(xs)` (cvc5 `SeqLength`).  The
sequence theory guarantees `len ≥ 0` intrinsically; no explicit assertion is needed
to prove `len(xs) ∈ Nat`.  `len` is only valid on Kleene-star (sequence) values;
applying it to any other value is a compile-time error.

*Combinations*:
- **Products containing `X*`** (e.g. `Nat* * Int`): `set_sort` recursively builds a
  `mk_tuple_sort([Seq Int, Int])`.  Membership projects with `ApplySelector`
  (not `child()`) so it works for both `mk_tuple` APPLY_CONSTRUCTOR terms and
  `SeqNth` results.
- **Kleene star of a product** (e.g. `(Nat * Nat)*`): element sort is a tuple sort;
  element membership uses the product recursion.
- **`X*` as a cross-kind union arm** (e.g. `Nat* | Int`): triggers the cross-kind
  union algebraic datatype (see below).  Same-sort sequences (`Nat* | Int*`, both
  `Seq Int`) do not build a DT — membership is a plain `OR` of quantified formulas.

*Cross-kind union datatype* (forward-compatible since this commit): the datatype
encoding was generalized from integer-leaf selectors to **one selector per arm of
the arm's natural CVC5 sort**.  This makes `Nat* | Int`, `(Nat * Nat) | Bool*`, and
future `Float32 | Int` all representable without touching the core DT builder.  See
`src/solver/sort.rs` for the forward-compatibility checklist for adding new sorts.

**Desugaring**: `X * N *` (Kleene star of a repeated product) correctly desugars the
inner `X * N` → `X * … * X` before wrapping in `KleeneStar`.

### Destructuring assignment (DECIDED)

Tuple values can be destructured into multiple bindings in one statement.
`mut` applies to all bindings in the pattern.

```
-- Immutable, no per-element constraints
x, y = (-3, 4)
x + y             -- 1

-- Immutable, per-element set constraints
x : Int, y : Nat = (-3, 4)   -- solver checks each element against its constraint

-- All-mutable destructuring
mut a : Int, b : Int = (p.0, p.1)
a := b            -- reassignment; b stays in its declared set

-- Destructuring reassignment of already-declared mutables
mut a : Int, b : Int = (10, 20)
a, b := (b, a)    -- swap
```

The LHS pattern requires no parentheses; the commas alone signal a destructure.
Parens on the RHS are required (consistent with tuple literal syntax).

**Constraints**: each binding may carry an optional `: Set` annotation that acts as
a membership proof obligation — identical in semantics to the constraint in `mut name : Set = expr`.

**`mut` scope**: `mut` before the first binding applies to every binding in the pattern (v0
keeps this simple; per-binding mutability is deferred).

**Reassignment (`a, b :=`)**: all names must have been declared with `mut`; set
constraints are checked for each element as with single-name `:=`.

**Partial destructuring**: when fewer binders are given than tuple elements, the last binder
collects the remaining elements as a sub-tuple.

```
a, rest = (1, 2, 3)   -- a = 1, rest = (2, 3)
rest.0                 -- 2
rest.1                 -- 3

-- With a constraint on the tail
a : Nat, rest : Nat * Nat = (p.0, p.1, p.2)
```

The tail binder can carry a set constraint (`rest : Nat * Nat`), which is checked as a proof
obligation in the same way as any per-element constraint.

**Deferred**: tuple-level constraint form `x, y : Int * Nat = (...)` (both constraints in one
annotation); nested destructuring `(x, (y, z)) = ...`; `_` wildcard; per-binding mutability.

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

### Function definition syntax (DECIDED)

Signature-then-body split. The signature is a first-class mathematical
statement about sets; the body names the parameters and provides the
implementation. The two are separate lines.

```
-- Signature: domain (as a set expression) and range
f : Int × Int -> Int
f(x, y) = x + y

-- Domain can be any set expression
safe_div : Int × (Int - {0}) -> Int
safe_div(x, y) = x / y

-- Overloading: multiple signatures, one shared body (§7).
-- Compiler checks each signature's domain/range independently.
abs : Nat    -> Nat
abs : NegInt -> Nat
abs(n) = if n >= 0 then n else -n
```

Domain forms accepted in a signature:
- Named set: `Int`, `Nat`, `Int16`, user-defined set names
- Cartesian product: `Int × Int` (ASCII: `Int * Int`)
- Set expression: `Int \ {0}`, `Nat | NegInt`, `{ n ∈ Int | n > 0 }`
- Compound: `{ (x, y) ∈ Int × Int | x + y < 100 }`

### Function body delimiters (DECIDED)

Two distinct forms; a function uses one or the other, not both at the
top level.

```
-- Pure / functional body: single expression after `=`
double : Int -> Int
double(x) = x * 2

-- Point-free is valid in `= expr` position (see §11 for composition
-- operator, which is still OPEN)
double = scale(2)   -- if scale(n)(x) = n * x

-- Imperative body: block of statements in `{ }`
-- Mutable locals are ONLY valid inside `{ }` blocks.
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0   -- Set annotation = declared loop invariant
    mut i: Nat   = 1
    while i <= n {
        acc := acc + i
        i   := i + 1
    }
    acc
}

-- Bare `{ }` blocks may appear anywhere inside a `{ }` body to
-- introduce a new scope.
f : Int -> Int
f(x) {
    {
        mut tmp: Int = x + 1
        -- tmp goes out of scope at the closing brace
    }
    x * 2
}
```

The `= expr` / `{ stmts }` split is a deliberate visual signal:
`=` marks a pure function; `{ }` marks one that does local mutation.

### Statement termination — bracket-depth newlines (DECIDED)

Newlines are the statement terminator. A `\n` at **paren-depth 0** ends the
current statement; a `\n` inside `(…)` or `[…]` is silently discarded, allowing
multi-line sub-expressions.

```
-- All fine — single-line statements:
x : Int = 1
a, b := (b, a)

-- Multi-line tuple or call: wrap in ( ):
result = (
    very_long_call(arg1, arg2)
    + another_call(arg3)
)

-- This is TWO statements (not a call):
a := b
(c, d)    -- parsed as a standalone tuple expression, not b(c, d)
```

`{` does **not** affect paren-depth. Set literals `{1, 2, 3}` and block
bodies `{ stmts }` both use `{}`; the set-literal parser explicitly skips
newlines between elements. A newline immediately after `{` inside a block
body terminates the preceding statement (if any) — block parsers call
`skip_newlines()` at the start and after each statement.

Alternatives considered and rejected:
- **Semicolons**: breaks the existing body of written Cantor code; inconsistent
  with the current aesthetic.
- **Go's trailing-token rule**: forces `{` placement; penalises certain
  formatting styles.
- **Haskell layout rule**: significant complexity; conflicts with Cantor's
  explicit `{}` blocks.

### Constants and zero-argument functions (DECIDED)

These are two distinct constructs with different syntax.

**Constants** — a named element of a set; not a function:

```
-- Signature and value on one line; no `->`.
pi   : Real = 3.14159
zero : Int  = 0

-- Constants can reference other constants (auto-inlined)
scale      : Nat = 1000
pi_scaled  : Nat = 3 * scale + 141

-- Compile-time set definitions share the same syntax
Colour = {1, 2, 3}
```

No `()`, no `->` in the signature. A constant has no domain or range —
it simply *is* an element of a set. Both value constants and named set
definitions use the same `name : Set = expr` / `name = expr` one-line form
and the same AST node; both are auto-inlined at compile time. Constants
are checked against their set annotation at compile time.

**Zero-argument functions** — a function callable at runtime; the `->` is
present but nothing precedes it (empty domain):

```
-- Signature: empty domain, explicit `->` distinguishes from a constant.
timestamp : -> Int
timestamp() = ...
```

The `()` on the implementation line distinguishes this from a constant.
Zero-arg functions may have `emits` (e.g. logging) in their `{ }` body.

**Auto-constexpr**: a zero-arg function with a `= expr` body (not `{ }`)
and no `emits` calls is automatically a compile-time constant — evaluated
once at compile time and inlined everywhere. The `{ }` / `= expr` split
already distinguishes pure from impure bodies, so no extra annotation is
needed.

**`Single`** — the named built-in singleton set `{★}`. Rarely needed in
practice (zero-arg functions use the empty-domain syntax; constants don't
reference `Single` at all), but available when the singleton must be named
explicitly as a first-class set value:

```
f : Single -> Int   -- same semantics as `f : -> Int`, domain made explicit
f(u) = 42
```

Both constants and zero-arg functions are implemented.

### `require`, `assert`, and `assume` statement syntax (DECIDED)

Statement form only — not function calls (see §4 for semantics).

```
require predicate   -- compile-time proof obligation; compile error if unprovable
assert  predicate   -- graduated: elide if proved, compile error if disproved,
                    --            runtime check + Class 1 error if unknown
assume  predicate   -- no check, no proof; compiler accepts the claim as a fact
```

`predicate` is any boolean expression: `x in Nat`, `lo < hi`, `x != 0`,
`a > 0 and b > 0`, etc. The statement adds the predicate as a fact for
the solver in all subsequent code within the enclosing scope.

The three-way distinction by outcome:

| | Proved (UNSAT ¬P) | Disproved (SAT ¬P, P never true) | Sometimes false |
|---|---|---|---|
| `require` | elide + add fact | compile error | compile error |
| `assert`  | elide + add fact | compile error | runtime check → `?` |
| `assume`  | add fact         | add fact      | add fact |

The "sometimes false" column covers the common `assert` case: the solver
finds a counter-model (¬P is satisfiable) but P itself is also satisfiable
(there exist inputs where it holds). The checker distinguishes "sometimes
false" from "always false" by running a second query: if ¬P is provable
(i.e. P is UNSAT), the assertion always fails → compile error. If P is
satisfiable, runtime behaviour decides → runtime check.

`require` is the right default when you know the invariant must hold
statically — it gives you a compile error rather than silently falling
through to runtime. Use `assert` when the invariant is program-input-
dependent (e.g. validating user input) and an unknown is acceptable.
Use `assume` only when you are certain the solver cannot prove it but you
are sure it is true.

Examples:

```
clamp : Int * Nat * NatPos -> Nat
clamp(x, lo, hi) {
    assert lo < hi         -- NOT statically provable: lo=5, hi=3 satisfies the
                           -- domain but violates the ordering. Runtime check;
                           -- returns a Class 1 error if the caller passes lo >= hi.
    result = if x < lo then lo else if x > hi then hi else x
    require result >= lo   -- static: solver can prove this from the if-chain
    require result <= hi   -- static: solver can prove this from the if-chain
    result
}

safe_to_nat : Int -> Nat | Fail
safe_to_nat(n) {
    assert n in Nat        -- unknown at compile time (n is any Int);
                           -- emits runtime check, returns Fail if n < 0
    n
}

caller : Int -> Nat | Fail
caller(n) {
    mut x: Nat = safe_to_nat(n)?   -- `?` propagates Fail if safe_to_nat fails
    x + 1
}
```

`require`/`assert`/`assume` are not functions because they produce no
output value — their effect is on the proof state (and optionally the
runtime), not on a value.

**`assert … else fail/return` (DECIDED)**: optionally pair with an else clause:

```
assert x > 0 else fail 400      -- return fail 400 on assertion failure
assert x > 0 else return -1     -- return -1 directly on assertion failure
```

The `else fail expr` form is only valid in functions whose range includes
`| Fail` or `!!` (i.e. declares a fallible return).  The `else return expr`
form is valid in any function and exits early with a success value.

### Loop syntax (DECIDED)

**`while` loops** — condition-guarded imperative loop. The `mut` invariant
annotation is used in three places: the initial value is checked against it,
each reassignment is checked, and after the loop the post-loop variable
inherits the invariant as a known solver fact. The compiler verifies the
inductive step (given the invariant and the loop condition, does one body
iteration maintain the invariant?).

```
while cond { stmts }
```

**`for x in S` loops** — iterates over a set, binding `x` to each element.
Works for both compile-time set literals and runtime `Set(T)` values.
Loop invariant semantics are identical to `while`.

```
for x in {1, 2, 3} { acc := acc + x }
for x in runtime_set { acc := acc + x }
```

Naming the loop variable with an uppercase letter (`for X in S`) promises
the value is known at compile time and forces the compiler to verify the
iterable is statically materializable — a lightweight opt-in to
guaranteed compile-time unrolling.

### Runtime sets (DECIDED)

`Set(Int)` and `Set(Bool)` are first-class heap-allocated runtime values.
They hold sorted, duplicate-free elements. Supported operations:

| Syntax | Meaning |
|---|---|
| `mut s: Set(Int) = {e1, e2, …}` | allocate; duplicates collapsed silently |
| `for x in s` | iterate in sorted order |
| `x in s` / `x not in s` | membership test |
| `size(s)` | cardinality |

The solver models runtime sets as opaque values: membership and `size`
are unconstrained integers, sufficient to prove `Int`-range signatures.

### `alias` and `distinct` (DECIDED)

Both modify how a name is treated at the set layer (§13). Syntax is a
one-line definition, same as any constant or named set:

```
-- alias: transparent rename; solver expands membership inline.
-- Colour is just another name for {1, 2, 3}.
Colour = {1, 2, 3}
Animal = alias Cat | Dog

-- distinct: creates a solver-opaque set disjoint from its basis.
-- Litre ≠ Float even though both have the same runtime Kind.
Litre = distinct Nat
```

`alias` is the right keyword (over `typedef`) as a deliberate signal to
reach for it less. `distinct` sets are currently phantom at the proof
level: the solver returns `unknown` for any signature involving one,
including the trivial identity `volume : Litre -> Litre`. Making them
useful requires uninterpreted SMT sorts and a constructor mechanism — see
the roadmap in §1/README.

## 11. Open questions

Syntax (next to design — treat as a group, not piecemeal):
- **Function composition operator** — `>>` (left-to-right, ASCII) and `∘`
  (right-to-left, Unicode) are the leading candidates. `>>` reads in the
  same direction as `f(x, y)` application. Choosing either frees `.` from
  namespace duty (module paths use `::` per §7). OPEN: confirm operator
  and decide whether partial application is needed to make point-free
  useful in practice.
- `raise` / `emits` statement syntax (incl. whether `emits` is one channel
  or several, and what the channel set is)
- Library interface declaration syntax (separate interface file vs inline
  visibility annotations — see §7)
- Aliasing/references to locals within the same function scope — leaning
  banned, not confirmed
- `decreasing by <measure>` annotation syntax (deferred past v0 but syntax
  should be consistent with `assert`/`assume` statement form when designed)

Other open items (lower priority, not blocking):
- Event type definition (built-in union vs user-definable)
- Concurrency/async event handling model
- Library interface versioning story (out of scope for now)
- Solver-capability versioning (deferred, nice-to-have)
- **Early `return` statement** — implemented (v0): `return expr` in a block
  body causes an immediate early exit with value `expr`. The SMT solver
  returns `Unknown` for any function body containing `return` (the linear
  block encoder cannot yet model control-flow that bypasses the tail position).
  Interaction with `?`/`Fail`: the returned value is used as-is; the caller
  applies its `?` checks to it normally.
- **Memory model direction** — leading candidate: persistent data structures
  → structural sharing → cheap diffing → easy reclamation; tracing GC
  during the diff phase (runs concurrently with IO). Mutable arena for
  within-event temporaries; arena is discarded at event boundary. (Not
  finalised — needs more design work when IO loop is tackled.)
- **Built-in containers** — pull in a library (`im`, `rpds`) or roll our
  own? Preference: start with flat arrays for temporaries; use `im`/`rpds`
  for persistent structures; roll our own later.
- **cvc5 proof effort / timeout** — decided: `cantor` exposes `--timeout <secs>`
  (default 60, `0` = unlimited) which maps to cvc5's `tlimit` option (ms) on
  every fresh solver instance.  A timed-out check returns `Unknown`.  Per-check
  resource limits (`rlimit`) are available in cvc5 but not yet exposed — they
  are deterministic (unaffected by system load) but harder to reason about.
- **`emits` and multithreading** — if concurrent IO threads share `emits`
  channels, synchronisation is needed. Defer until threading model is decided.

## 12. Explicitly deferred future features (not in scope, do not implement
    speculatively)

- `decreasing by <measure>` annotation for recursive sets (tier 2) and
  automatic measure inference (tier 3)
- Termination checking for recursive functions (three-tier
  proven/disproven/unproven + `-Wall` escalation)
- Automatic domain-partition inference for overload sets
- Emit handlers written in Cantor itself
- Solver-capability versioning
- **Named product sets (structs)** — `Point = distinct (x: Meter; y: Meter)`;
  constructor syntax TBD (tentatively positional `(3m, 4m)` or named
  `(x = 3m; y = 4m)`). Projection via dot: `p.x` (natural as a named
  projection function). Requires namespace support first. (Anonymous tuples
  with positional projection are DONE — see §10 "Product set values (tuples)".
- **Named union sets** — `Measurement = distinct (Length: Meter | Volume: Liter)`;
  constructor via injection: `Measurement.Length(3m)`. Parallel to named
  products; requires namespaces. Aligns with products/coproducts: products
  have projections, coproducts have injections.
- **Literal suffixes** — `3m` for `3 meters` etc.; sugar for a constructor
  call. Design depends on named product sets landing first.
- **Pattern matching** — `match x { a => …, b => … }` or overloaded-signature
  form; exact syntax undecided. Natural complement to named unions.
- **Destructuring** — implemented in v0 (see §10 "Destructuring assignment").
  `for i, x in collection` falls out as sugar over destructuring + for-in (deferred).
- **Generics via `given`** — `given A; require A <= Countable; f(x: A) -> Nat`.
  Introduce a compile-time variable into scope; obligations stated with
  `require`; instantiation substitutes concrete values and asks the solver
  to discharge them. Reduces to an overload generator with no new semantic
  machinery. Single new keyword: `given`. (Design explored but not finalised.)
- **Pattern matching** — see above.
- **Early `return` extended solver modelling** — `return` is implemented at the
  codegen level but the solver reports `Unknown` for block bodies containing it.
  Full solver support requires modelling early exits as SSA phi-merge paths.
- **`raise` / `emits` syntax** — see §11.
- Float, char/string, byte primitive values.
- BigInt runtime support for unbounded `Int` / `Nat`.
- Compiled (AOT) binaries; linker integration.
- Module system (imports, separate checking) — see §7.
- More containers: ordered sets, vectors, maps; iterators.

## 13. Primitive types and numeric tower

### Value layers (DECIDED)

Every value in Cantor passes through three distinct conceptual layers:

1. **Names** — what the developer writes: `Bool`, `Nat`, `Litre`, `alias Metre`.
   Many names may point to the same underlying set (aliases) or to entirely distinct sets.

2. **Sets** — the solver's unit of identity.
   `3 litres` and the integer `3` are in different sets even if both have the same runtime representation.
   The SMT solver works exclusively at this layer and has no notion of runtime representation.
   `distinct` creates a new set distinct from its basis set (`Litre ≠ Float`).
   `alias` creates a new name pointing to an *existing* set — fully transparent to the solver.

3. **Runtime Kind** — what codegen emits: `Kind::Int` (`i64`), `Kind::Bool` (`i1`), `Kind::Float` (`f64`, future), `Kind::Set` (heap allocation, future).
   Kind is a **codegen-only** concept; the solver never sees it.
   `Kind` is derived from the set via a deterministic `set_kind(set_expr) -> Kind` lookup.
   `distinct` does not create a new Kind — `Litre` maps to `Kind::Float` just as `Float` does;
   the solver enforces their distinctness without codegen needing to know.

**Consequence for aliases:** `alias Metre = Float` is a transparent rename at the set layer.
Error messages show the name at the point of the error (Clang-style), not the underlying set.
The `alias` keyword (over `typedef`) is a deliberate stylistic signal to reach for it less.

**Consequence for `Bool`:** `Bool` maps to `Kind::Bool` (`i1`).
The solver treats `Bool`-domain parameters using `boolean_sort`, not integer sort.
No implicit coercion between `Bool` and any integer kind exists at any layer.

### Single

- **`Single`** — the singleton set `{★}`, containing exactly one element.
  Rarely written explicitly; see §10 "Constants and zero-argument functions"
  for when it arises.

### Bool

- `Bool = {true, false}` — a generative set with exactly two elements.
- **Disjoint from all integer types.** No implicit coercion between `Bool`
  and any integer exists anywhere in the language (see §10 gotchas).
- `==` on `Bool` is structural set equality (same as everything else —
  no special case).
- **Runtime representation: `i1`.** Bool values are a distinct Kind
  (`Kind::Bool`) and are stored as LLVM `i1`.
- **Uniform `i64` ABI at function boundaries.** All function parameters
  and return values cross LLVM call boundaries as `i64`.
  Bool params are widened to `i64` at the call site and truncated back to
  `i1` in the callee's entry block.
  Bool return values are widened to `i64` before the `ret` instruction and
  truncated back to `i1` by the caller immediately after the call.
  This keeps the calling convention uniform while preserving Bool's
  structural distinctness throughout the body.
- **Solver representation: `boolean_sort`.** Bool-domain parameters are
  created as cvc5 constants in the `boolean_sort` (not integer sort),
  so boolean operators (`and`, `or`, `not`, comparisons) work without
  sort mismatches.  Domain membership is trivially satisfied by sort
  construction and requires no extra `membership_constraint` assertion.
  Bool-returning call results use a `boolean_sort` fresh variable so
  callee contracts propagate correctly.

### Integers

- **`Int`** — the mathematical integers ℤ, unbounded. The default integer
  type. All integer literals have domain `Int` unless a narrower domain is
  imposed by context (function signature, `assert`, etc.).
- **`Int8`, `Int16`, `Int32`, `Int64`** — generative subsets of `Int`:
  `Int16 = { n ∈ ℤ | -32768 ≤ n ≤ 32767 }`, and analogously for other
  widths. These are not distinct types — they are named generative sets
  used as domain/range annotations.
- At runtime, a value whose domain is proven ⊆ `IntN` is stored in the
  corresponding LLVM integer type (`i8`, `i16`, `i32`, `i64`) for
  performance. Domain is `Int` (unbounded) → `i64` for v0; full BigInt
  is deferred.

### Arithmetic widening

- `+`, `-`, `*` operate in ℤ — exact and never overflow at the semantic
  level.
- The solver automatically proves: `a ∈ IntN ∧ b ∈ IntN → a + b ∈ Int(2N)`.
- **Cap at Int64**: `Int64 + Int64 → Int` (not `Int128`). 128-bit
  hardware support is inconsistent; `Int` (BigInt) is the correct
  mathematical fallback. Same cap applies to the other arithmetic operators.
- `/` is integer division (truncates toward zero). Domain excludes zero in
  the denominator — standard domain-check machinery handles this.

### Narrowing back to IntN

Three mechanisms in order of increasing programmer responsibility:

1. **`assert expr in Int16`** — inserts a runtime range check; failure is
   a Class 1 domain-violation error. The solver may statically eliminate
   the check if it can prove the assertion holds (or reject compilation if
   it can prove it doesn't).

2. **`truncate16(x)`** — a built-in with declared type `Int → Int16`,
   defined as 2's-complement modular reduction. The solver always proves
   its range is `Int16` — no `assert`/`assume` needed at the call site.
   This is the correct tool when **wrapping behaviour is semantically
   intended** (e.g. fixed-width hardware arithmetic, hash functions).
   Codegen: `truncate16(a + b)` where `a, b : Int16` lowers to a single
   native `i16 add` with overflow. `assert (a + b) in Int16` lowers to
   `i32 add` + a bounds check (two instructions, no wrap).

3. **`assume expr in Int16`** — no runtime check; the programmer asserts
   domain membership to the proof system only. Use only when the solver
   cannot prove containment but the programmer is certain. Unsound if
   wrong — produces silently incorrect results at runtime, same as
   `assume` everywhere else in the language (§4).

### Error handling wire format

- **`Fail`** — built-in singleton set representing the failure tag. A fallible
  function declares `Fail` in its range: `f : Int -> Nat | Fail`.
  - `fail` (bare) — produces `{i1=1, i64=0}` at the LLVM level.
  - `fail expr` — a typed failure with integer payload: `{i1=1, i64=expr}`.
    Success `n` and `fail n` are always distinct because the i1 flag differs.
  - At the LLVM level, any function whose range includes `Fail` (directly or
    via `!!`) returns a `{i1, i64}` struct. Flag i1=0 means success (payload
    is the return value); flag i1=1 means failure (payload is the error code,
    or 0 for a bare `fail`).

- **`!!` error-union** — `Success !! ErrorSet` desugars at parse time to
  `Success | (Fail * ErrorSet)`. No offset encoding, no runtime decoding:
  the failure struct carries the error code directly in the i64 payload field.
  The solver treats `Fail * ErrorSet` union arms using membership constraints
  on the product set.

- Named domain-specific error sets (e.g. `HTTPError = {400, 503}`) are
  user-defined sets. `T | HTTPError` and `T !! HTTPError` are both represented
  as `{i1, i64}` at runtime; the error code propagates at face value via `?`.
  `T | HTTPError` is plain set union (success values may overlap error codes
  numerically, distinguished only by the flag). `T !! HTTPError` desugars to
  `T | (Fail * HTTPError)` and has the same wire format.

### Natural numbers and other named subsets

- **`Nat`** — `{ n ∈ ℤ | n ≥ 0 }` — natural numbers *including* zero.
  `abs : Int -> Nat` is therefore correct: `abs(0) = 0 ∈ Nat`. ✓
- **`NatPos`** — `{ n ∈ ℤ | n > 0 }` — strictly positive integers (excludes
  zero). DECIDED: name is `NatPos`.
- **`NonZeroInt`** — `{ n ∈ ℤ | n ≠ 0 }` — all integers except zero.
  The declared domain of the `/` built-in's right argument. Useful whenever
  a function accepts any non-zero integer, positive or negative
  (e.g. `safe_recip : NonZeroInt -> Int`). Distinguished from `NatPos`
  in that it includes negative values.
- All of the above are generative subsets of `Int` — not separate numeric types.

### Chained comparisons (resolved)

`a < b < c` parses as `(a < b) < c` (left-associative per §10). The
domain of `<` requires both arguments to be in a numeric set; `a < b`
produces `Bool`, which is disjoint from all numeric sets (above). The
domain checker rejects this as a domain violation — there is no implicit
`Bool → Int` coercion to rescue it. The intended idiom is
`a < b and b < c`.
Future diagnostic (not v0): detect the chained-comparison pattern and
suggest the `and` form explicitly.

## 14. REPL (DECIDED)

Running `cantor` with no arguments starts an interactive REPL.

- **Prompt**: `ℵ> ` (primary), `   ` (continuation for multi-line input)
- **Multi-line**: the REPL detects incomplete input (EOF parse error) and
  continues reading. A signature line (`foo : Int -> Int`) followed by the
  implementation (`foo(x) = x + 1`) is entered naturally over two lines.
- **Definitions**: any valid top-level item (function with signatures, name
  constant, set alias) is added to the session environment and verified
  immediately. The verification result (proved / counterexample / unknown)
  is shown for every annotated signature. Set aliases with no constraints
  are confirmed with `defined`.
- **Redefinition**: re-entering a name silently replaces the previous
  definition (GHCi style). The verification report covers only the new item.
- **Expression evaluation**: bare expressions are evaluated and the result
  printed. Only Int-returning expressions are supported for now; Bool
  results are shown as 0/1, and tuple-returning expressions will produce
  an error from LLVM verification.
  TODO: infer result kind from the expression for correct Bool/Tuple display.
- **Commands**: `:help`/`:h`, `:defs`, `:reset`, `:quit`/`:q`. Ctrl-D exits.
- **State**: the REPL re-runs SMT checking over all accumulated items each
  time a new definition is added. Simple and correct; optimise later if needed.
- **LLVM**: a fresh LLVM Context and JIT engine are created for each
  expression evaluation. Module IR is validated before JIT compilation so
  that broken codegen paths produce a clean error rather than undefined
  behaviour.

## 15. Prototype approach

- Build via a **unit-test suite for the compiler** rather than a polished
  first syntax — syntax is expected to be reworked multiple times before
  settling, so tests should target semantic behavior/diagnostics over exact
  surface syntax where possible, to reduce churn cost across rewrites.
- v0 feature scope per the staged decisions above: structural-recursion-only
  for recursive sets, no termination checking for recursive functions, core
  three-class error model, static sets + basic comprehensions, library-level
  compilation with disjoint overloads.
