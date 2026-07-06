# Recursive Set Definitions: Research + Implementation Plan

**Status:** Phase 0 (well-foundedness check, §7) DONE 2026-07-06 —
`src/semantics/wellfounded.rs`, 9 semantics tests + 4 CLI e2e tests, all green,
zero regressions in the existing 1000+ test suite. Phases 1-3 (solver encoding,
runtime boxing, narrowing/consumption) not started.
**Scope:** design-decisions.md §3 "Recursive sets", tier 1 (structural recursion) only —
this is the one variant explicitly slated for v0; tiers 2/3 (`decreasing by`, automatic
measure inference) stay deferred exactly as already agreed.

**Correction, found while implementing Phase 0 (see §2 below):** the first draft
of this document mis-stated the well-foundedness rule as "every recursive
occurrence must be a direct operand of `*`", and consequently mis-classified
`Weird = Weird | Int` as *rejected*. It's actually accepted — Cantor's shipped
cross-kind-union encoding gives every `|`-arm its own CVC5 constructor
regardless of shape, so a bare self-reference arm is exactly as well-founded as
a product-guarded one (it's the `Peano = Zero | Peano` shape, not Russell's
barber). §2 below is corrected in place; `wellfounded.rs`'s doc comment and
`tests/semantics/wellfounded_tests.rs::bare_self_reference_arm_alongside_a_base_arm_is_well_founded`
both call this out explicitly as a regression test for the correction.

This document exists to turn the one-paragraph sketch already agreed in
design-decisions.md §3 and the "generating sets" fixpoint sketch in backlog.md into
something concrete enough to implement in ordered, reviewable steps. Nothing here
overrides those documents; it fills in the "how" underneath the "what."

---

## 1. Why this is the right thing to plan next

Two things made this the standout candidate among the backlog items, once I started
reading the actual code rather than just the wishlist:

1. **The design decision already exists but the "how" doesn't.** §3 commits to tier-1
   structural recursion for v0 and gives a real example (`BinStr`), but nothing in
   `src/` acts on it yet — `NameDef` only has `DefKind::Alias` and `DefKind::Distinct`,
   there is no third case, and no code walks a set definition looking for a
   self-reference.
2. **Most of the hard infrastructure already exists, aimed at a different feature.**
   `docs/tagged-union-ir-plan.md` (all 6 steps DONE) already builds a genuine CVC5
   algebraic datatype with one constructor per union arm for cross-kind unions like
   `(Nat * Nat) | Nat` — see `build_union_datatype_sort` in `src/solver/sort.rs`. That
   is 80% of the machinery a recursive set needs. The remaining 20% (self-referential
   constructor fields) turns out to already be supported by the underlying `cvc5`
   Rust crate we depend on — see §4 below. So this isn't "invent a new subsystem," it's
   "generalize one that shipped a few weeks ago, plus close one representation gap
   (boxing) that the existing subsystem was never asked to handle."

That combination — a real, previously-unresolved design question, sitting one
generalization-step away from a bar the codebase has already cleared — is what made
me want to work on this over, say, generics/`given` (already has a settled sketch and
is mostly "go implement it") or macros/compiler-functions (fun, but much more
speculative — the "well-foundedness" angle here is the part I found genuinely meaty).

---

## 2. What "structural recursion" means precisely (tier 1 only)

From §3: a recursive occurrence must be **strictly under a constructor**. The first
draft of this plan over-read that as a syntactic rule ("a direct operand of `*`");
implementing Phase 0 forced a more careful look, and the actual rule is more
permissive — see the correction below. Concretely, for a named set definition
`Name = E[Name]` (E containing zero or more occurrences of `Name`, at any position
reachable through top-level `|`-arms and `*`-factors):

- **Allowed**: every `|`-arm of `Name`'s definition either mentions no recursive
  names at all, or mentions them only as bare Cartesian-product factors.
  `Tree = Int | Tree * Tree` (both `Tree`s inside a `*`) — but **also**
  `Weird = Weird | Int` (bare self-reference *alongside* a base arm — see the
  correction below for why this is fine, not a mistake).
- **Allowed** (mutual recursion, falls out for free — see §4): `Tree = Int | Forest`,
  `Forest = {} | Tree * Forest`.
- **Rejected, hard error "cannot verify well-foundedness"**: every `|`-arm depends,
  directly or transitively, on the name itself with **no base arm anywhere in the
  cycle** — `Weird = Weird` (not even a union, pure regress), `Tree = Tree * Tree`
  (product-only, no `Leaf`-like case — the algebraic-datatype analogue of
  `data Tree = Node Tree Tree` with no base constructor, uninhabited by any finite
  value), or `A = B` / `B = A` (mutual, neither side ever bottoms out).
- **Rejected, "not yet supported"**: a recursive reference that appears somewhere
  *other* than a bare union arm or Cartesian-product factor — nested under `&`, `-`,
  inside a comprehension, etc. This is non-structural (or at least a shape the tier-1
  classifier doesn't attempt to reason about) — not silently accepted, not silently
  rejected as ill-founded either, since neither claim would be justified.

**Correction, found while implementing this check (`src/semantics/wellfounded.rs`):**
the "strictly under a constructor" requirement does *not* mean the recursive
occurrence must be a literal operand of `*`. Cantor's shipped cross-kind-union
encoding (`build_union_datatype_sort`, src/solver/sort.rs) already gives **every**
`|`-arm its own CVC5 constructor, regardless of whether that arm is a bare name or a
product — there is no structural difference between "arm is `Tree*Tree`" and "arm is
bare `Tree`" as far as the constructor-per-arm scheme is concerned. So a bare
self-reference arm is exactly as well-founded as a product-guarded one: `Weird =
Weird | Int` is isomorphic to unary-encoded ℕ (`Peano = Zero | Succ(Peano)`, i.e.
`Peano = Zero | Peano` with the `Succ` wrapping implicit in the arm's own
constructor), not Russell's-barber-shaped. The one genuine requirement — matching
backlog.md's original "generating sets" sketch exactly, with no extra syntactic
gloss on top — is that **at least one `|`-arm per name in the cycle must bottom out
without depending on the cycle**.

**Key realization while reading the CVC5 API (§4): we don't need to reinvent the
generating-SCC fixpoint from backlog.md as a bespoke algorithm.** CVC5's inductive
datatype theory *already* requires exactly this property to accept a datatype
declaration as well-founded (every recursive datatype must have at least one
non-recursive "way out," or the sort has no ground terms and CVC5 either rejects it
or reports it uninhabited). So the compiler-side well-foundedness check can be
implemented as: **flatten each name's definition into `|`-arms and, within each arm,
`*`-factors; find which names are reachable from themselves at all (any operator,
any nesting — the safety net); then, restricted to those, run the generating-set
fixpoint over the flattened arm/factor structure** — which is precisely backlog.md's
algorithm, now justified as *mirroring CVC5's own acceptance criterion* rather than
an independently-invented rule, and implemented exactly this way (§7, Phase 0, DONE).
Doing our own check first (rather than only finding out from a solver-side rejection)
is still worth it for two reasons: (a) it lets us give a good compile-time error
message before ever touching the solver, matching the "compiler confirms this
explicitly to the developer" promise in §3; (b) mutual recursion across many
definitions in one SCC needs a topological/SCC-shaped pass regardless of what CVC5
does, to know what order to build `mk_unresolved_dt_sort` placeholders in (Phase 1).

---

## 3. AST / elaboration changes

Today (`src/ast.rs`): `NameDef.kind : DefKind` is `Alias | Distinct`. Definitions are
collected into a flat `NameDefs` HashMap in one pass in `elaborate.rs` (line ~66)
*before* any individual definition is elaborated — so name lookup by symbol already
doesn't depend on declaration order, which is good news: forward references and
literal self-references are already resolvable as raw AST lookups. What breaks today
is the *recursive resolution* functions (`set_kind`, `set_sort`) — they recursively
walk into a `Var`'s definition with no visited-set/in-progress tracking, so a
self-referential definition would infinite-loop them as-is.

Planned changes:

1. **New `DefKind::Recursive { ctor_arms: Vec<...> }` variant** (or a parallel
   `SemNameDef` annotation added post-elaboration — leaning toward keeping `ast::NameDef`
   unchanged and detecting recursion during elaboration into `SemanticTree`, since
   "is this recursive" is a derived fact, not something the parser needs to know
   syntactically — `Tree = Int | Tree * Tree` parses with zero new grammar).
2. **A pre-pass over all `NameDef`s** before individual elaboration: build the
   dependency graph (name → set of names it mentions as direct operands of `*`),
   compute SCCs (standard Tarjan), classify each SCC as `NonRecursive` (singleton, no
   self-edge) or `Recursive` (size > 1, or singleton with a self-edge), and for each
   `Recursive` SCC run the generating check from §2. A non-generating SCC is a hard
   `CompileError::Diagnostic` (user error — this is not an ICE, it's the developer
   writing an ill-founded definition), not a panic.
3. **Threading a "currently resolving" set through `set_kind`/`set_sort`.** This is
   the one piece of real plumbing surgery: both functions need an extra
   `in_progress: &HashSet<Symbol>` (or similar) parameter so that hitting `Var(self)`
   while `self` is in `in_progress` returns "this is the recursive-occurrence marker"
   instead of recursing forever. Natural fit for the existing `EncodeCtx`/`CheckCtx`
   context-struct pattern already used elsewhere in this codebase for exactly this
   kind of "one more piece of context threaded through everything" problem.

---

## 4. Solver encoding — the good news

`src/solver/sort.rs::build_union_datatype_sort` already builds a CVC5 algebraic
datatype for cross-kind unions, one constructor per arm, via `tm.mk_dt_decl` /
`tm.mk_dt_cons_decl` / `ctor.add_selector`. What it cannot do today is let a
selector's sort be *the datatype currently being built* — every selector sort comes
from `set_sort` on an already-fully-resolved arm expression.

I checked the underlying `cvc5` crate (`~/.cargo/registry/.../cvc5-0.4.0`) rather than
assuming, and it already exposes exactly the primitives needed, with a working
integration test (`dt_mutual_recursion`, `cvc5-0.4.0/tests/integration.rs:1176`) that
is a near-verbatim match for what Cantor needs:

```rust
// Tree = Leaf(Int) | Node(Forest)  ~  Forest = Empty | Cons(Tree, Forest)
let forest_unres = tm.mk_unresolved_dt_sort("Forest", 0);
let tree_unres = tm.mk_unresolved_dt_sort("Tree", 0);

let mut leaf = tm.mk_dt_cons_decl("Leaf");
leaf.add_selector("val", tm.integer_sort());
let mut node = tm.mk_dt_cons_decl("Node");
node.add_selector("children", forest_unres.clone());
let mut tree_decl = tm.mk_dt_decl("Tree", false);
tree_decl.add_constructor(&leaf);
tree_decl.add_constructor(&node);

let empty = tm.mk_dt_cons_decl("Empty");
let mut fcons = tm.mk_dt_cons_decl("FCons");
fcons.add_selector("head", tree_unres);
fcons.add_selector_unresolved("tail", "Forest");   // <-- self-reference by name
let mut forest_decl = tm.mk_dt_decl("Forest", false);
forest_decl.add_constructor(&empty);
forest_decl.add_constructor(&fcons);

let sorts = tm.mk_dt_sorts(&[tree_decl, forest_decl]);  // resolves all mutual refs at once
```

So the plan for `sort.rs` is: generalize `build_union_datatype_sort` into something
like `build_recursive_datatype_sorts(scc: &[Symbol], ...)` that:

1. Calls `mk_unresolved_dt_sort(name, 0)` for every name in the SCC up front.
2. Builds each constructor exactly as `build_union_datatype_sort` does today, except
   a selector whose arm is `Var(other_name_in_scc)` uses `add_selector_unresolved`
   (or the already-created unresolved sort handle) instead of calling `set_sort`
   recursively.
3. Calls `mk_dt_sorts` once for the whole SCC, and caches the resulting `Sort` per
   name (this replaces the current one-sort-per-lookup `set_sort` call for these
   names — needs a cache keyed by SCC, resolved once per solver session, mirroring
   how `distinct_preds`/`SolverPreds` are already threaded through as a shared cache).

Non-recursive cross-kind unions keep using `build_union_datatype_sort` completely
unchanged — this is purely additive.

**Membership encoding** generalizes the same way: `membership_constraint_for_dt`
already does `ApplyTester ∧ field_constraints`; for a recursive selector, the field
constraint is just "is a member of `Tree`'s own membership predicate," which is only
well-defined if `Tree`'s membership predicate is expressed as CVC5 syntactic
well-formedness of the recursive datatype sort itself (i.e. "any value of this CVC5
sort is automatically a well-founded Tree" — true by construction, no induction
needed at the SMT level, because CVC5's datatype semantics already bakes in
acyclicity/well-foundedness for every value of an inductive datatype sort). This is
the same realization as §2: CVC5's datatype theory is *already* the proof of
well-foundedness; Cantor's job is to detect ill-founded definitions before they'd be
rejected by CVC5, and to translate its own union/product syntax into the datatype
declaration shape CVC5 expects.

---

## 5. Runtime representation — the one genuine gap (boxing)

This is where the existing tagged-union work (`docs/tagged-union-ir-plan.md`) can't
be reused unmodified, and where I want to flag the scope honestly rather than
undersell it.

`Kind::TaggedUnion(Vec<Kind>)` today flattens every arm into a **statically-known,
finite** number of `i64` leaves (`leaf_count`), because arm kinds are always
non-recursive — `(Nat * Nat) | Nat` has a compile-time-fixed max of 2 leaves. A
recursive arm has no such bound: a `Tree` value can be arbitrarily deep, so a `Tree *
Tree` constructor field cannot be flattened into N leaves at compile time — it must
be a **pointer** to a heap-allocated node, one level of indirection per recursive
occurrence, exactly like `Box<Node>` in Rust or a boxed enum in any ML-family
language.

Concretely this needs:

- A new `Kind` shape for recursive positions — tentatively `Kind::Boxed(Box<Kind>)`
  or a dedicated `Kind::Recursive(Symbol)` used only for the field(s) that close a
  cycle in the dependency graph (all other, non-recursive fields of the same
  constructor keep flattening exactly as today — this is a targeted fix, not a
  rewrite of `TaggedUnion`).
- A minimal heap object per constructor application: `{ i32 tag, <flattened
  non-recursive leaves>, <boxed pointers for recursive leaves> }`, allocated once per
  `Tree.node(l, r)`-shaped construction (today's untagged-by-name constructor call —
  see §6) and read back via the existing `extract_tagged_union_arm` /
  `extract_tag` primitives, which already operate at the "opaque i64 pointer" level
  for `Vector`/struct-vec heap objects, so this is following an established pattern,
  not inventing a new one.
- **Explicitly out of scope for this plan**: any deallocation/reclamation strategy.
  This project doesn't have one yet for `Vector`/struct heap objects either (worth
  double-checking against the runtime code before implementation, not assumed here
  with full confidence), and the backlog's own "memory model" open question
  (persistent structures → sharing → cheap diffing → tracing-GC-during-diff) is
  explicitly unresolved. Recursive sets should use whatever the prototype's current
  answer is (leak, most likely) and not attempt to jump ahead on the memory-model
  question — that's a separate, larger open question this plan deliberately doesn't
  try to close.

---

## 6. Construction and consumption — reusing shipped features instead of waiting on two deferred ones

This is the part of the plan I'm most pleased with, because it changes what "v0
recursive sets" can honestly promise.

Two backlog items look like prerequisites at first glance — **named unions with
constructor syntax** (`Measurement.Length(3m)`) and **pattern matching**
(`match x { ... }`) — both explicitly deferred, per design-decisions.md §12. If
recursive sets actually needed either one, this would balloon into a three-feature
project. I don't think they do, for v0:

- **Construction** already works today for cross-kind unions with no special syntax:
  a plain tuple literal or scalar coerces into whichever arm matches its `Kind`, via
  `maybe_coerce`/`coerce_to_union_dt` (§`tagged-union-ir-plan.md` steps 4–5). Nothing
  new needed here beyond making sure a recursive arm's `Kind` (§5, boxed) is one of
  the coercion targets.
- **Consumption** can piggyback on two features that already exist independently:
  the `in` membership test against a union arm (`compile_tagged_union_membership` /
  `membership_constraint_for_dt`, already implemented) for narrowing, and tuple
  **destructuring assignment** (already DECIDED and implemented per §10 of
  design-decisions.md) for pulling fields out once narrowed:

  ```
  Tree = Int | Tree * Tree

  size : Tree -> Nat
  size(t) {
      if t in Int { return 1 }
      l, r = t              -- only reachable once `t` is provably `Tree * Tree`
      return size(l) + size(r) + 1
  }
  ```

  For a 2-arm union this narrowing is trivial (CVC5 testers are exhaustive by
  construction, so "not arm 0" implies "arm 1" for free); for N-arm unions it
  generalizes to a chain of `if`/`else if` exactly the way any exhaustiveness
  argument would, without needing a dedicated `match` construct. This needs the
  solver's existing path-sensitive obligation/narrowing machinery (the same kind of
  thing that already narrows `x` after `assert x in Nat`) taught one more fact: "in
  the `else` of `if t in Int`, `t`'s arm is known to be the tuple arm" — genuinely
  new work, but it's an extension of an existing mechanism, not a new one.

If this turns out to be harder than it looks once someone (me, in a follow-up
session, or whoever picks this up) is elbow-deep in `blocks.rs`/`obligations.rs`, the
fallback is to ship recursive sets as *construction/signature-proof only* for v0
(prove a `build_tree` function's range is `Tree`, without yet being able to write a
`size` function that consumes one) and land narrowing separately — still a coherent,
useful, honestly-scoped slice, just smaller. I'd rather flag that fallback now than
discover it's needed halfway through and have it look like scope creep.

---

## 7. Phased implementation (parser / solver / codegen, per CLAUDE.md's preferred split)

**Phase 0 — well-foundedness check only, no solver/codegen changes. DONE 2026-07-06.**
`src/semantics/wellfounded.rs`, called as the first step of `elaborate()` (before the
`fn_sigs` pass, since that's the first thing that would otherwise recurse forever on
a self-referential name). Two layers, matching §2's corrected algorithm exactly:
a generic reachability walk (`for_each_var`/`find_cyclic_names`) that catches *any*
cycle regardless of shape (the safety net — this is what makes the ill-founded and
unrecognized-shape cases fail loudly instead of hanging), and the generating-set
fixpoint (`classify`) restricted to whatever that walk flags, using
`ast::flatten_union`/`ast::flatten_domain` to read off `|`-arms and `*`-factors.
New `CompileError::IllFoundedRecursiveSet` variant for the permanent rejection;
the "well-founded but not implemented" and "unrecognized shape" cases both reuse
the existing `Unsupported` variant with a distinguishing message.
Tests: `tests/semantics/wellfounded_tests.rs` (9 tests — every case in §2's
allowed/rejected/unsupported list, including a dedicated regression test for the
`Weird = Weird | Int` correction) and `tests/cli/recursive_sets.rs` (4 end-to-end
tests confirming the CLI reports a clean diagnostic, not a hang or an ICE). Zero
regressions across the pre-existing 1000+ test suite. As hoped, this phase turned
out small, self-contained, and independently valuable regardless of whether phases
1-3 ever land: it turns today's "infinite loop"/stack-overflow failure mode for a
self-referential definition into a clean diagnostic.

**Phase 1 — solver encoding.** `build_recursive_datatype_sorts` in `sort.rs` per §4;
extend `membership_constraint_for_dt` for recursive selectors; extend counterexample
extraction (currently has a `TaggedUnion => 0` placeholder per
`tagged-union-ir-plan.md` — recursive datatypes need their own placeholder path,
printing something like `Tree.node(Tree.leaf(1), Tree.leaf(2))` is a nice-to-have,
not required for correctness). Test: domain/range proofs for functions that
*construct* trees (`build : Nat -> Tree`) without consuming them — this exercises
the sort/membership machinery in isolation from §6's narrowing question.

**Phase 2 — codegen (construction).** `Kind::Boxed`/heap node representation per §5;
constructor-call codegen reusing `build_tagged_union_value`/`extract_tagged_union_arm`
patterns. Test: JIT-run a tree-building function and confirm the returned pointer
round-trips through `len`/field-access primitives at the Rust FFI boundary (mirroring
how existing `Vector` codegen tests call the C ABI functions directly to check
contents).

**Phase 3 — narrowing/consumption** per §6, as its own step since it's the part with
the most open design risk (extending path-sensitive obligations). If this phase
turns out to be substantially harder than phases 0–2, ship without it per the
fallback in §6 and file it as a tracked follow-up rather than blocking the rest.

---

## 8. Explicitly out of scope

- `decreasing by <measure>` (tier 2) and automatic measure inference (tier 3) — §3
  already defers these; this plan doesn't touch them.
- Named-union constructor syntax (`Tree.Node(l, r)`) and general `match` — §6 argues
  v0 doesn't need either; both remain independently deferred features for whoever
  eventually wants nicer surface syntax over what this plan makes possible.
- Any memory-reclamation strategy for the new boxed nodes.
- Deriving anything (`Arithmetic`, `Ordered`, etc.) over recursive sets.
- Mutual recursion is *handled* by the SCC framing (§2–§4) but not specifically
  tested beyond the `Tree`/`Forest` shape already validated in the underlying `cvc5`
  crate's own test — real Cantor-level mutual-recursion tests are Phase 1+ work, not
  a separate phase.

## 9. Open questions for you, before implementation starts

1. **Is the `if t in Int { ... } / l, r = t` consumption story (§6) actually the
   syntax you want**, or would you rather v0 recursive sets ship
   construction-only and wait for real pattern matching? I lean toward "ship the
   narrowing reuse trick" because it makes the feature immediately useful, but it's
   very much a taste call, not a correctness one.
2. **Naming for the boxed `Kind` variant** (§5) — `Kind::Boxed(Box<Kind>)` vs.
   something more specific like `Kind::Recursive(Symbol)`. I'd lean toward the latter
   since it can carry the recursive set's name for better error messages and
   debug-printing, but it's a small decision either way.
3. Whether recursive named sets should be allowed to also carry an explicit
   `distinct` (probably not — §4's argument is that they're structurally
   transparent to the solver, like `X*`, not opaque like user `distinct`, so
   `distinct Tree = Int | Tree * Tree` would be a contradiction in terms worth
   rejecting with a clear message rather than silently accepting).
