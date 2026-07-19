This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do

- ordered guard groups: static call-site resolution to a direct call
  (`solver::encode_call::push_overload_call_obligation`) is unconditionally
  disabled for a call whose candidates belong to an ordered group — every
  such call always goes through the runtime dispatch chain, even when the
  argument is a literal the solver could place in exactly one arm. The
  existing "is candidate i's domain provable for every value reaching this
  call site, tried in order" shortcut isn't sound once domains may overlap
  (a trailing wildcard is unconditionally provable, which doesn't mean it's
  the first-declared match for every value) — a real fix needs an extra
  proof that no *earlier* candidate could also match for the same reaching
  values, which is more solver machinery than the first cut of this feature
  warranted. Found via CLI end-to-end testing (a call routed through an
  unconstrained parameter silently resolved to the wrong arm) — see the
  `fix: ordered guard group calls must never statically resolve` commit.
- more testing
  - some property based tests! we have a lot of unit tests but could go further, `proptest` crate recommended
  - fuzzing too, `cargo-fuzz` crate recommended
  - snapshot testing, i.e. output
    ```
    foo.ast
    foo.semantic
    foo.constraints
    foo.kinds
    foo.ll
    ```
    and so we can see exactly what a refactor changed, `insta` crate recommended
  - Lots nice built in static analysis
    -  `cargo udeps` and `cargo machete`
    -  `cargo deny` for vulns, dupes and licensing
    -  `cargo +nightly miri test` for UB, aliasing, invalid references
  - "giving every stage a `validate()` method"
- `check pred(x) for x in X` keyword for property based testing, unit testing as the degenerate case. Sits between `assert` and `require` in strength. Maybe `check ... or assume` for another assume variation.
- termination checking on recursion and loops with a 'decreases n' annotation to declare a ranking function.
  automatic inference of the ranking function structurally where possible
- more set comprehensions features
  - math syntax `{x*2 | x ∈ Nat, x > 0}` as sugar for the python form (deferred)
  - multi-binder `{x+y for x in A for y in B}` desugaring to Cartesian product (deferred)
- list comprehensions
- generators at runtime. we can relax restriction on infinite 
  sets being compile-time only, under the restriction that they have a generator.
  generator for totally ordered, well founded built in sets (Nat, Bool, not Int?) come for free
- collections direction (DECIDED 2026-07-06):
  - no `<1, 2, 3>` ordered-set literal: `<`/`>` clash with comparison operators
    (the C++ template ambiguity), and runtime sets already iterate in a
    deterministic sorted order. Orderedness is a *property* of a set — a set
    paired with an enumerator — not a bracket. `OrderedSet(X)`,
    `FiniteOrderedSet(X)` and `InfiniteOrderedSet(X) == UniqueGenerator(X)`.
  - bags/multisets need no bracket either: `Bag(X) = X* / sort` — the quotient
    of sequences by permutation, reusing the quotient-set machinery. The
    ordered × unique 2×2 grid of collections is exactly quotient-by-permutation
    × quotient-by-multiplicity of `X*`. Bag literals are just `[…]` sequence
    literals in a Bag-annotated position, canonicalized to sorted order.
    Ergonomics (derived ops) deliberately deferred until quotient-set
    `deriving` machinery exists.
  - the pair view of a sequence (`['a', 'b']` ↔ `{(0, 'a'), (1, 'b')}`) is a
    *coercion, not an equality* — same doctrine as sequence unification
    (equality would make `x in xs`, `len` vs `size`, and `for x in xs`
    ambiguous). The view is reified explicitly by `graph(xs) : (Nat * X)*`,
    the graph of the sequence-as-function; later generalizes to
    `graph(f) == {(a, f(a))}` for functions. `enumerate(xs)` will be kept as a
    beginner-friendly synonym, and `zip(Nat, xs)` becomes the general form
    once generators land. None of the three is implemented yet.
- `X*`/`X^ == Generator(X)` for finite and infinite sequences 
- immutable set constants like `s = {1, 2, 3}`, need to be baked in as statics
- value literals desugaring in compile time set positions and support for sequences of literal values.
  E.g.
  - `Nat* - {[]}`
  - more ambitiously `Nat* - {4}`/`Nat* - {[4]}`/`Nat* - {(4)}` as all coercing to the same thing
    "My vector can be anything except a length 1 list containing a 4".
    I don't expect the solver to work very well in the last case, but we should at least
    let the user try and write it.
- more basic values:
  - `Int32`, `Int(32)` and their Nat cousins as LLVM iN values, right now all are i64.
  - `Float32` and `Float64` as distinct sets, `FiniteFloat32` and explicit `posZero`, `negZero`, `nan` values
  - `SignedN`, `UnsignedN` for N != 32
  - `Char` ordering comparisons
  - a packed UTF-8 representation for `Char*` (currently a boxed-i64-per-character)
  - `Byte`, `Bits32`, `Bits(435)` generic etc
  - `Size`, `Word` (platform dependent)
- use `distinct` to define `Hex` and then implement a `show : Hex -> Char*` overload.
  Formatting will need higher order functions to let us wrap/decorate the format call:
  ```
  Formatter = Char* -> Char*
  
  given A
  uppercase : A -> Formatter * A
  uppercase(x) = (toupper, x)
  
  given A
  show : Formatter * A -> Char*
  show(f, x) = f(show(x))
  ```
- more containers:
  - maps
  - ordered sets and bags — see "collections direction" above
  - deques and stuff like that?
- more operators:
  - bitwise ops on bytes
  - comparison operators (they are in the lexer but I don't think they are implemented)
- `Rational` support, including making `/` for `Int` return `Rational`
  - adding `quot` and `rem` to keep `Int` inside `Int`
  - division soundness issue for ints, need to ensure cvc5 and codegen agree
- operator overloading for things like `List(Byte)`?
  - custom operator overloading syntax like with haskell? I don't care for inventing new ops but supporting existing ones might be important
  - automatic operator overloading for disinct sets, like allowing arithmetic on Litre. See `deriving` below.
- constants JIT'd instead of at rust level to get consistency 
- human intros (familiar with types, newbie with the word type taboo'd) and LLM intro. The human intros would be good to include a bunch of Venn diagrams and ye olde curved arrows between ovals representing functions to visualise the concepts along the way.
- error messages
  - review and improve error messages
  - suggested constraints in error messages
  - counterexample printing TODOs
- recursive set definitions: **Is this already done?**
  ```
  Tree = Int | Tree * Tree
  Vector : {} | X * Vector
  ```
  where the second is just the same as `X*`
  Some rules: no recursion in set comprehension predicates to ban Russell's barber.
  We will need to extend this to a cycle check on the graph of comprehension dependencies, prior to the solver.
  Some way to verify that structural definitions like the above are well founded, even with mutual references:
  > Every recursively-defined set that is intended to be inhabited must be generating.
Algorithm:
1. Mark every set with a production consisting entirely of already-known finite sets as generating.
2. Repeat until no new sets become generating.
3. Reject any recursive SCC (strongly connected component) that never becomes generating.
- Allow splitting huge arrow data up for performance, each chunk is an array
  * vector → balanced tree of chunks
  * set → hash table of chunks
  * map → hash table of key/value chunks
  * string → rope of UTF-8 chunks
- could also add: tuple-level constraint `x, y : Int * Nat = ...`; nested patterns; `_` wildcard; per-binding mutability
- along with recursive set definitions we get should allow constructors in binders
  ```
  Tree = leaf: Int | leaf2: (X * Y) | node: (Tree * Tree)

  size(x, y : X, Y) = ...
  size(Tree.leaf2(x, y)) = ..
  ```
  Started prototyping this (2026-07-18, session_014Qh7K9iYP6WY8zKzc8VcjK) as step 4 of the
  pattern-matching plan, using only Int-Kind-compatible named-union arms (see "named union
  sets" above) — `size(Shape.Circle(r)) = ...` desugaring to a guard-style comprehension
  domain (`{r for r in Shape if from(r) in Circle'sBasis}`), reusing guards' machinery.
  Reverted before landing: `r` inside the body has *solver* sort `Shape` (uninterpreted),
  not `Nat`, even though `from` is a runtime no-op — so `r * r`-style arithmetic on the
  raw pattern binder is a genuine sort mismatch, not just a missing SMT encoding. Fixing
  it needs either a real `let r = from(param)` rewrite prepended to the body (hygiene-aware
  — must not capture an inner rebinding of `r`, e.g. a nested comprehension) or a different
  design entirely. Two genuine, general, independently-useful bugs *were* found and fixed
  along the way and are already shipped: `solver::sort::set_sort`'s `Comprehension` arm
  hardcoded `integer_sort()` regardless of source (now delegates to the source's own sort),
  and `solver::membership::encode_comp_expr` had no `from(x)` support in a filter at all.

  **Update (2026-07-18, later session)**: `distinct`'s Int-only basis assumption — the thing
  flagged above as blocking a tuple/cross-kind arm — is now lifted for the *single
  homogeneous Kind* case (`kind::is_distinct_basis_representable`,
  `solver::preds::build_distinct_preds`'s two-pass `mk_D`/`from_D` sort resolution): `distinct`
  can now wrap `Bool`, `Char`, a tuple, a vector, or a `distinct`-over-`distinct` chain, and a
  named union's arms can share any one of those Kinds (not just `Int`), see
  `tests/solver/distinct_basis.rs`. Still NOT lifted: a named union whose arms have
  *genuinely different* Kinds from each other (`Circle: Nat | Rect: Nat * Nat`) — `Shape`
  would need to become a real tagged-union-shaped `distinct` (wrap/unwrap via the arm's own
  `ck_*` constructor before/after `mk_Shape`/`from_Shape`, mirroring
  `solver::sort::build_union_datatype_sort`), which is genuinely new solver *and* codegen
  work, not a hardcode removal — so this is still the right next step for resuming step 4,
  now with one fewer prerequisite in the way. Two more bugs found (and fixed) while lifting
  the basis restriction, both worth rereading before similar work: `solver::sort::set_sort`'s
  `Var` arm checked `kind_of == Bool` *before* checking whether the var was a registered
  `distinct` name, so a `distinct Bool` set was silently treated as the builtin `Bool` sort
  itself; and `encode_call.rs`'s constructor blocks passed an array literal straight to
  `mk_D` without coercing it to a `Seq` first (array literals always encode as a plain CVC5
  tuple unless something downstream asks for a sequence — ordinary function calls get this
  bridging for free from `membership_constraint`, but `ApplyUf` doesn't bridge).

  A third bug was found the same way and turned out to be more than a curiosity — it's
  **FIXED**, same session: `solver::sort::set_sort`'s `Union` arm treated **any** union with a
  tuple arm as cross-kind (needs the tagged-datatype wrapper), even when both arms have the
  *identical* tuple shape (`(Nat*Nat) | (Nat*Nat)`) — `kind::union_if_distinct` correctly
  dedups this to a bare `Kind::Tuple` at the Kind level, so codegen already treated it as
  untagged, but `set_sort` didn't check `ls == rs` the way it already did for the sequence
  case right below it in the same match. Two live consequences, not just a plain-code
  curiosity: on ordinary (non-`distinct`) code, `.0`/`.1` projection on such a value came back
  a fabricated counterexample for a provably-valid program
  (`tests/solver/cross_kind_unions.rs::identical_shape_tuple_union_domain_projection_proved`);
  on a `distinct` named union with two same-shape tuple-arm labels (squarely inside this
  session's own newly-lifted scope), it crashed `cvc5` outright — a raw C++-level abort, not
  even a catchable Rust panic — because `mk_Shape`'s declared domain sort (the wrongly-cross-
  kind DT) didn't match the plain-tuple argument term
  (`tests/solver/distinct_basis.rs::named_union_tuple_arms_same_shape_proved`). Fixed by
  gating both the tuple and (for parity) the general-DT cross-kind conditions on `ls != rs`,
  same shape as the sequence/Bool checks already next to them.

  **Update (2026-07-18, same day, third session)**: heterogeneous-Kind named-union arms
  (`Circle: Nat | Rect: Nat * Nat`) are now **DONE** —
  `tests/solver/heterogeneous_named_unions.rs`,
  `tests/cli/heterogeneous_named_unions.rs`. Turned out smaller than expected: `kind::set_kind`,
  `solver::preds::build_distinct_preds`, `from(x)`'s solver *and* codegen encoding, and
  `sort::build_union_datatype_sort` were all *already* fully generic once the elaboration gate
  (`semantics::elaborate::validate_distinct_basis`, née the `is_distinct_basis_representable`
  check) allowed a `Kind::TaggedUnion` basis through for a labeled def. The two genuinely new
  pieces were the constructor on each side: solver (`encode_call.rs`'s `coerce_arg_to_basis`)
  now wraps the argument into the union DT's matching arm constructor via
  `sort::maybe_coerce`/`coerce_to_union_dt` before `ApplyUf(mk_Shape, …)`; codegen
  (`expr_call.rs`'s `Name.Label(x)` block) now builds the real `{ i32 tag, i64 leaves }` struct
  via the *already-existing* `coerce::build_tagged_union_value` (previously only reachable from
  ordinary `A | B` coercion) instead of the same-Kind case's pure passthrough, driven by a new
  `Compiler::named_union_arms` table (`compile.rs`, populated the same `kind::set_kind`-over-a-
  local-`ast::NameDefs` way `elaborate.rs` computes Kind, no solver dependency).

  **Update (2026-07-18, fourth session): the pairwise-distinctness v0 scope cut is now
  LIFTED** — `Circle: Nat | Square: NatPos | Rect: Nat * Nat` (two `Int`-Kind arms mixed with a
  `Tuple`-Kind one) is accepted and proved. The suspected constructor-naming-collision bug
  turned out to be real, but not where first suspected: the domain-membership check itself
  (`membership_constraint_for_dt`'s name-based lookup, `t ∈ whole_union`) is actually sound even
  with colliding constructor names — `(P∧Q1)∨(P∧Q2) = P∧(Q1∨Q2)` holds regardless of whether the
  two disjuncts happen to share a tester, so the `f : Nat | NatPos | (Nat*Nat) -> Int` smoke test
  never could have shown a wrong proof. The real bug was in the *labeled constructor* call site:
  `encode_call.rs`'s `coerce_arg_to_basis` wrapped a constructor's argument into the union DT by
  matching CVC5 *sort* (`sort::coerce_to_union_dt`), not by label — so `Shape.Circle(5)` and
  `Shape.Square(5)` (both `Int`-sorted) always resolved to the *same* physical constructor
  regardless of which label was called, making them the literally identical CVC5 term.
  Confirmed with the pairwise check temporarily disabled: `assert Shape.Circle(5) !=
  Shape.Square(5)` was wrongly reported "always fails" — a genuine solver-level soundness bug,
  not just a cosmetic naming collision. `codegen::compile::compile_elaborated` had an
  independent, unrelated bug on the same feature: `Compiler::named_union_arms` zipped `labels`
  (one per syntactic arm) against `kind::set_kind`'s *Kind-deduped* whole-union arm list, so any
  named union with a real duplicate-Kind pair tripped an `assert_eq!` panic on every run — dead
  code until this session, since the elaboration check above always rejected the input that
  would reach it.

  Fixed with three changes, in order: (1) `solver::encode_call::coerce_arg_to_labeled_arm` —
  given the labeled constructor's already-known arm index (`named_union_arm_for_constructor` now
  returns it), builds `ApplyConstructor` directly against that position instead of searching by
  sort; the basis-obligation check also had to move to *before* this wrapping (checking the raw
  argument against the arm's own natural sort), since checking it after wrapping hit
  `membership_constraint`'s DT fast path with a mismatched single-arm-list assumption and wrongly
  rejected `Shape.Square(1)` (a genuine regression caught by the CLI/solver tests below, not
  shipped). (2) `solver::membership_seq::membership_constraint_for_dt` now matches a union DT's
  constructors by *position* (`dt.constructor(i)` against `flatten_any_union(set_expr)[i]`,
  provably the same list/order `build_union_datatype_sort` used) instead of by name — makes it
  robust to the naming collision directly, no longer relying on the "sound anyway" argument
  above. (3) `kind::named_union_value_kind` (new, called from `set_kind`'s own `Var` arm so
  nested `alias` references pick it up for free) reports one Kind per *syntactic* label for a
  labeled `distinct` union, instead of `set_kind`'s ordinary Kind-deduping `Union` handling —
  fixes both `codegen::compile`'s `named_union_arms` table (now just calls this) and every other
  site that asks "what Kind is a `Shape` value" (e.g. a function's declared `-> Shape` range),
  which is what the `assert_eq!` panic and a later ICE (`coerce_to_kind: value kind
  TaggedUnion([Int, Int, Tuple(...)]) does not match any arm of [Int, Tuple(...)]`) both actually
  were. Tests: `tests/solver/heterogeneous_named_unions.rs` (soundness regression guard +
  second-same-Kind-arm basis-obligation guard), `tests/cli/heterogeneous_named_unions.rs`
  (`heterogeneous_named_union_duplicate_kind.cantor`, full pipeline).

  **Also found and fixed along the way, unrelated to `distinct`/labels at all**:
  `kind::merge_if_branches`'s `AppendThenArm`/`AppendElseArm` cases (an ordinary `if`/`else if`/
  `else` chain merging a new branch into an existing `TaggedUnion`) pushed the new arm's Kind
  *unconditionally*, unlike the sibling `MergeTaggedUnions` case a few lines above it, which
  already deduped — so a plain 3-way `if` chain revisiting a Kind (`if a then 5 else if b then 6
  else (3, 4)`, no `distinct`/labels anywhere) produced a `TaggedUnion` with a duplicate-Kind arm
  and ICE'd in codegen's `coerce_to_kind`. This is arguably the same underlying "duplicate-Kind
  arm in a TaggedUnion" hazard the entry above worried about, but reachable in totally ordinary
  code and via the value-Kind-merge path rather than the named-union-basis path. Fixed by adding
  the same dedup `IfMerge::AppendThenArm`/`AppendElseArm` now carry a `then_tag`/`else_tag` field
  (the existing arm's index on a Kind match, or the freshly-appended index otherwise) instead of
  codegen always assuming "append at the end". Tests:
  `tests/semantics/elaborate_tests.rs::if_extends_tagged_union_with_arm_matching_an_existing_kind`,
  `tests/solver/if_else.rs` (two tests, including one confirming the reused arm's own range
  obligation is still checked, not silently dropped), `tests/cli/if_kind_merge.rs`.

  **Also found, out of scope, not fixed**: projecting into a specific arm after `from()` (e.g.
  `from(Shape.Rect((3,4))).0`) is *not* provable today — confirmed this is a general,
  pre-existing limitation of cross-kind-union narrowing, not `distinct`-specific: the plain
  non-`distinct` equivalent (`g : -> (Nat*Nat) | Nat; g() = (3, 4); main() = g().0`) hits the
  identical "not in Nat" false counterexample. This is the same narrowing gap already flagged
  by the reverted step-4 constructor-pattern prototype above (`let r = from(param)` rewrite, or
  a different design) — round-trip correctness for heterogeneous arms is instead verified via
  `show()` (real per-arm runtime tag dispatch, commit `6210702`), which *does* work end to end
  and confirms both the tag and the packed leaf values are correct without needing narrowing.

  **Update (2026-07-18, fifth session): labeled arms are now always tag-forced, even when every
  arm shares a Kind.** Resuming step 4 (constructor patterns) as a prerequisite: a *purely*
  same-Kind labeled union (`Circle: Nat | Radius: NatPos`, no other differing-Kind arm mixed in)
  had **no runtime tag at all** — `Shape.Circle(3)` and `Shape.Radius(3)` were the literally
  identical value, since `parser::items::parse_distinct_value` folded labeled arms with `|`, and
  `|` only builds a cross-kind CVC5 datatype when the arms' *sorts* genuinely differ
  (`solver::sort::set_sort`'s `Union | DisjointUnion` arm). Fixed by folding labeled arms with
  `+` instead (`BinOp::Add`/`DisjointUnion`) — the operator that already means "always force a
  tag, never dedup by sort" at the Kind layer (`kind.rs`'s `BinOp::Add` arm) — plus generalizing
  `ast::flatten_union` (renamed `ast::flatten_any_union`) to recurse into `BinOp::Add` too, so
  its two AST-level callers (`kind::named_union_value_kind`, `semantics::wellfounded`) still see
  one entry per arm. New regression test:
  `tests/solver/named_unions.rs::named_union_same_kind_labels_stay_distinct_proved`.

  Tried forcing the DT unconditionally for *every* `DisjointUnion` at the `solver::sort::set_sort`
  layer first (matching `kind.rs`'s own unconditional behavior) — reverted, it broke a wide swath
  of already-shipped, unrelated `+` domain/range proofs (`{0} + NatPos -> Nat`-style signatures in
  `tests/solver/membership.rs`/`set_ops.rs`): once a same-sort `+`-value's *solver sort* is a DT,
  proving a DT-sorted parameter satisfies a plain scalar return Kind (`x ∈ Nat`) hits the exact
  narrowing gap two paragraphs up — so forcing it everywhere would have silently traded working
  code for that different, larger, already-deferred gap. The fix is instead scoped narrowly to
  `solver::preds::build_distinct_preds`'s basis-sort computation (`build_union_datatype_sort`
  called directly for `def.labels.is_some()`, bypassing `set_sort`'s general same-sort-fallthrough)
  — this only affects a labeled `distinct` def's own `mk_D`/`from_D` sort, not ordinary `+` used
  directly in a signature.

  **Also found while verifying the fix end-to-end (CLI/codegen, not just the solver proof),
  confirmed real but deliberately NOT fixed as part of this change** — filed here for a dedicated
  follow-up: `==`/`!=` between two `Kind::TaggedUnion` values is unsound at codegen.
  `codegen::expr::compile_binop`'s generic comparison path (`scalarize_to_int` on both operands)
  calls `narrow_tagged_union` for a `TaggedUnion` operand, which drops the tag and keeps only the
  payload — so `Shape.Circle(3) != Shape.Radius(3)` is solver-*proved* true but runtime-*computes*
  false (`main() = 0`, confirmed via `cargo run -- run` on a throwaway file — not currently
  covered by any checked-in test). This is old, general code, not something this session's fix
  introduced, but it was practically **unreachable** before labeled constructors existed: an
  anonymous `+` value only ever reaches a specific arm through coercion, which always
  self-selects the *one* arm the value actually satisfies — so two anonymous `+` values could
  never end up in *different* arms while sharing the same payload, and the tag-blind comparison
  happened to always give the right answer by coincidence. Labeled constructors are the first
  thing that lets a user *deliberately* force two overlapping-range same-Kind arms
  (`Circle: Nat`/`Radius: NatPos` both admit `3`) — exactly what this session's fix makes a
  headline, tested property (`Shape.Circle(5) != Shape.Radius(5)` is a checked-in solver
  regression guard) — so the codegen gap is now directly reachable and undermines that property
  at runtime, even though the solver proof itself is sound. A real fix needs either (a) tag-first
  comparison with a per-arm branch that only compares the *active* arm's own leaves (avoiding
  `undef` payload bits in unused trailing leaf slots — comparing those directly is its own LLVM
  IR hazard), mirroring `codegen::show`'s existing per-arm tag-dispatch structure, or (b) making
  every `TaggedUnion` construction site zero-fill unused leaves instead of leaving them `undef`,
  which would make a simple full-struct comparison safe. Worked around for now in
  `tests/cantor_files/named_union_shape.cantor`/`tests/cli/named_unions.rs` by testing
  construction + `show()` only, not `!=` — `show()` doesn't expose the label in its output
  either (same payload prints identically for `Circle(3)`/`Radius(3)`), so it can't demonstrate
  distinctness, only that both labeled constructors compile and run without crashing.

  **Update (2026-07-18, sixth session): step 4 (constructor patterns) is DONE for the
  statically-resolvable case** — `size(Tree.leaf2(x, y)) = ...` from the very top of this
  backlog entry now works, e.g.:
  ```
  Shape = distinct (Circle: Nat | Rect: Nat * Nat)
  area : Shape -> Nat
  area(Shape.Circle(r)) = r * r
  area : Shape -> Nat
  area(Shape.Rect(x, y)) = x * y
  main : -> Nat
  main() = area(Shape.Circle(3)) + area(Shape.Rect((4, 5)))  -- proved, runs, = 29
  ```
  Scoped to **non-recursive** named unions (recursive sets aren't implemented past the Phase 0
  well-foundedness check) and to call sites where the argument's arm is visible at the call site
  (a literal constructor, or — transitively — anything the solver can already resolve
  statically). See docs/design-decisions.md for the user-facing writeup.

  Design: `Name.Label(x, ...)` in parameter position parses into a `CtorPattern`
  (`ast::Param::ctor_pattern`) carrying the union name, label, and binder names, with the
  parameter itself renamed to a synthesized `__pat{index}` (mirrors the `__lit{index}`
  literal-arm convention). `semantics::elaborate::desugar_param_patterns` narrows that
  parameter's domain to `{__patN for __patN in <declared slice> if tester(__patN) and
  extractor(__patN) in <arm's own basis>}`, where `tester`/`extractor` are two new internal-
  only synthesized callees (`{Union}.{Label}?`/`{Union}.{Label}!`, never lexed, so no
  collision with the real `?` postfix operator) resolved by two new blocks in
  `elaborate::builtin_call_kind`, `solver::encode_call::encode_call`, and
  `codegen::expr_call::compile_call` — mirroring the existing `Name.Label(x)` constructor
  block exactly, just dispatching on `ApplyTester`/`ApplySelector` at the label's known
  `arm_idx` instead of building the tagged value. `build_ctor_pattern_prelude` (also in
  elaborate.rs) prepends a `Stmt::Let` (scalar arm) or `Stmt::DestructLet` (tuple arm, one
  binding per element) to the function body, extracting the arm's payload into the pattern's
  own binder names via the same extractor call — `FunctionBody::Expr` bodies get wrapped into
  a synthesized `FunctionBody::Block` for this. `solver::disjointness::
  fresh_overload_param_terms` gained a `TaggedUnion` case (building the fresh per-position
  solver constant via `set_sort` on the candidate's own declared domain part, not from `Kind`
  alone — two unrelated named unions could share the same abstract `Kind::TaggedUnion` shape)
  so overload-disjointness proofs between two labeled-arm overloads of the same function work,
  closing a `TODO: only scalar... Lift together if ever needed` that was written during the
  int-soundness-plan phase 2 work and finally became needed here.
  `codegen::overload_dispatch::compile_domain_part_match` was generalized from `IntValue` to
  `BasicValueEnum` (a `TaggedUnion` argument is a struct, not a scalar register) so the
  existing runtime-dispatch chain doesn't panic if it's ever reached for a constructor-pattern
  parameter — retained even though (see below) no currently-provable program reaches it for a
  `TaggedUnion` position; a correctness improvement over the previous unconditional
  `.into_int_value()`, and forward-looking for if the axiom gap below is ever closed.

  **Major dead end, worth remembering**: the natural next step — proving a call like
  `area(pick(b))` where `pick`'s return value's arm isn't visible at the call site (every
  function is verified in isolation; `pick`'s call *contract* only says "result ∈ Shape", not
  which arm) — needs a fact like "any `Shape` value tagged `Circle` has a payload in `Nat`" to
  hold for an *opaque* term, not just the pattern-matched function's own parameter. Tried
  asserting this as a universally-quantified axiom once per labeled union, per arm (∀y:the
  union's basis DT sort. is_Circle(y) → payload(y)∈Nat), alongside `build_distinct_preds`,
  sound in principle (the only way to construct such a value is through the labeled
  constructor, which already independently enforces the same obligation at its own call
  site) — **reverted**: reproducibly, quantifying over a custom algebraic datatype sort with
  an *arithmetic* body (anything beyond a trivial `→ true`) made cvc5 report the **entire
  assertion set as inconsistent** — both a claim and its negation came back "Proved"
  simultaneously, confirmed with a minimal hand-built reproduction using the `cvc5` crate
  directly (no Cantor-specific code at all), independent of `mbqi`/`nl-cov`/shared-selector-
  naming/timeout settings. This is NOT the same class of thing as the already-known "narrowing"
  gap a few paragraphs up (that one degrades safely to `Unknown`/counterexample) — the axiom
  actively made false things provable, strictly worse than not having it. Left reverted; indirect
  calls to a constructor-pattern function honestly report `Unknown`/counterexample instead
  (safe, just incomplete). If this is ever revisited: the working theory is something about
  `Forall` + `ApplyTester`/`ApplySelector` (datatype theory) + an arithmetic (`Geq`) body
  together confuses cvc5's quantifier instantiation in this version/binding — worth checking
  a newer cvc5 release, or a differently-shaped encoding (e.g. asserting the fact as a
  ground/per-call obligation threaded through call contracts instead of a blanket `Forall`,
  which is a real solver-architecture change, not a quick fix).
- more IO backends: CLI, TUI, web, SDL, OpenGL, vulkan, etc
- write-only side effects via `emit`
- compiled binaries
- linker integration
  - ChatGPT says that rust makes crates instantiate generics only when they are used, we should do the same
  - so we will need to ship all the instantiations, the source (or an IR) for any generics, and the domain/range constraints
  - we can do this for the "under the hood" overloads too, like `Int64` vs `BigInt`. If a package doesn't statically make
  use of the `BigInt` overloads then we can put those in as generics and let them instantiate on use
- FFI particularly useful for defining Output handlers
- enums. like distinct these create new distinct values. Sugar for distinct Nat with named values?
  ```
  enum {a, b, c} -- no value provided, auto derive from Nat
  enum {a, b, c = 5}
  enum Nat {a, b, c} -- explicit auto derive from Nat
  enum String {red, green, blue, bloo = "I am bad at spelling"} -- auto derive "red" from string
  Foo = distinct {one = 1, two = 2, three = 3} -- named constants Foo.one etc for set literals
  ```
- literal suffix support for e.g. 3m for 3 meters
- structs/"named product sets". product sets are either fully not named or fully named.
  (named union sets — `Measurement = distinct (length: Meter | volume: Liter)` with
  `Measurement.length(3m)` construction — are DONE, including arms of genuinely different
  Kinds from each other, e.g. a hypothetical `length: Meter | corners: (Nat*Nat)`, and arms
  that share a Kind with each other, see the "constructors in binders" entry above)
  Tentative syntax for products:
  ```
  Pair = distinct Meter * Meter
  mut p : Pair = (3m, 4m)

  Point = distinct (
      x: Meter
    * y: Meter
  )
  mut p : Point = (x = 3m, y = 4m)
  ```
- automatic range inference
- pattern matching with `match x { a => ... , b => ...}`?
- higher order functions: X -> Y is already the set of functions from X -> Y and we can use Haskell precedence rules for X -> Y -> Z.
- partial application via `_` as a placeholder `add(_, 1)` or `sub(1, _)` or `f(x, _, y, _)`
- infix operators as named functions `(+)(1, 2)`, combines nicely `_` with as a placeholder 
- once we have higher order functions we can add 'Litre = distinct Float32 deriving Ordered + Arithmetic + Printable' 
  by letting the compiler apply the litre isomorphism to any relevant slot in the domain and its inverse if Float32 is in the range
- then we could add quotient sets! IntMod5 = Int / (x, y -> (x - y) rem 5 == 0) deriving Arithmetic gives us a ring!
  but needs to be Int / (x -> x rem 5) so the compiler knows how to produce a canonical representation
  we can also allow `X * Y / X` to desugar to `X * Y / (t -> t.1)` etc as long as we can determine the projection structurally.
  "If the compiler can prove L = X * R for some X, then L / R is shorthand for quotienting by the canonical projection onto X."
- struct member functions?
  ```
  Point = distinct Nat * Nat

  Point.length : Point -> Float32
  Point.length(x, y) = sqrt(x*x + y*y)

  p : Point
  p.length() -- same as Point.length(p), namespace lookup driven by known or inferred range of p
  ```
  errors would be reported like
  ```
  v is not in the domain of ?.length
  domain Point | Road for ?.length constructed from:
    Point.length : Point -> Float32
    Road.length : Road -> Float32
  ```
- lambdas and closures
  - lambda syntax is just `x -> x + 1` with automatic domain and range inference
  - domain constraints are just `(x : Int) -> x + 1`
  - range constraints are a bit awkward as they would need one of
    ```
    (x -> x + 5) : (X -> Y)
    (x : X) -> ((x + 5) : Y)
    ```
    I think the first is slightly less ugly until we get automatic inference
  - closures capture everything used within the body of the lambda. They capture mutables by reference, _unless_ they escape via the funcion return in which case they take ownership of the captured variables and copies of the constants.
- ~macros~ - "compiler functions". what is a natural Cantor way of doing code generation? functions that manipulate ASTs? yes! we can make them work on the `SemanticTree`! post elaboration, but before constraint checking.
  > Compilation itself becomes a computation over ordinary values.
  > A semantic tree is just another value. A compile-time transformation is just another function. The compiler is simply evaluating functions whose domains happen to be compiler data structures.
  So for example:
  ```
  double: Expression -> Expression
  double(x) = x * 2
  ```
  where the overloads of a function must be either all compile-time, or all runtime. This is so that `double(a + b)` is unambigous.
  We call them "compiler functions" because they are just functions run in the compiler :-)
- generics. do we need mechanisms to help define functions that work on lots of different sets? seems like it should work alongside overloading.
  Went through this with ChatGPT and ended up with something quite elegant:
  ```
  population:
    given A : Set(Countable)
    Habitat(A) -> Nat

  population:
    given A
    require A in Set(Countable)
    Habit(A) -> Nat

  population:
    given A
    require A <= Countable
    Habit(A) -> Nat
  ```
  We introduce a sole new keyword `given` to define _compile-time variables_ that are introduced into the lexical scope.
  The solver then defers the constraint checks until instantiation time.
  The is very similar to overloading - we have simply defined an _overload generator_.
  I like this observation from ChatGPT:
  > The thing that's striking me about this whole design is how little new machinery you've introduced. In most languages, generics are a completely separate subsystem with their own syntax, name resolution, constraint language, instantiation rules and error model. Here, they seem to reduce to just three ideas:
  >
  > 1. given introduces a symbolic compile-time value.
  > 2. require states obligations about it.
  > 3. Instantiation substitutes concrete values and asks the solver to discharge those obligations.
  >
  > Everything else—monomorphisation, overload generation, even "generic constraints"—falls out as implementation details. That's about as small a conceptual core as I can imagine, and it fits remarkably well with the direction Cantor has been taking.
  Then we can do the equivalent of typeclasses too
  ```
  given A Tree(A) = A | Tree(A) * Tree(A)
  ```
  assuming we also have recursive set definitions from above
- To support the equivalent of type classes we will also need a way to define "open sets". E.g.
  class Functor f where  
    fmap :: (a -> b) -> f a -> f b  
  In Cantor we should have Functor be an "open set"?
  I.e.
  given A, B, F
  require F in Functor
  map : (A -> B) * F(A) -> F(B)
  what exactly is Functor then? A set of what?
  I suppose F is a compile time function! while A/B is a compile time set
  The syntax might just be 'open Functor' at the global scope (rather than _within_ the function def), so
  ```
  open Functor 
  given A, B, F
  require F in Functor
  map : (A -> B) * F(A) -> F(B)
  ```
  then instantiation will check that F is in Functor 
  We define values within Functor by declaring it to be true:
  ```
  (*) in Functor
  ```
  not sure how we interpret that to be the Kleene star?
  That should cover all of list, option and error tuples etc.
- Extend Fable's `equiv` to cover any proof obligation:
  forall is:
  ```
  given x : Int
  given y : Int
  require P(x, y)
  ```
  there exists is
  ```
  y = choose { y if P(y) }
  ```
- multiple concurrent IO threads? ChatGPT convo suggests developing a _scheduler_ using optimisitic
  concurrency control, taking adaptive measurements on which events conflicts, both statically and dynamically determining state partitions for different event handlers, letting the developer declare that events are `ordered` or `unordered` or `mostly independent` so that we know the "shape" of events. Lots of fun stuff we could do!
- small runtime sets optimized as bitmasks. Once we get to the homogeneous set level the runtime 
  doesn't actually care what the values are. So a cardinality 64 set can be encoded as just a uint64.
  It may make sense to extend this to fairly large sets with vectors of uint64.
  It would be nice to benchmark when this breaks down (time space tradeoff right?)
- Allow the solver to provide facts to the codegen to allow optimizations or simplify its code.
  ```
    The key lever: assumptions become optimisations

    LLVM aggressively exploits things like:

    noalias
    nonnull
    range metadata
    llvm.assume
    alignment guarantees

    These are all essentially:

    “trusted facts about the program”

    So if Cantor can prove things like:

    this function is pure
    this loop is independent
    this container is contiguous
    this index is within bounds

    then Cantor can emit:

    stronger IR annotations
    fewer conservative branches
    more vectorisation opportunities
  ```

# To learn

- More about LLVM features so I can make better use of them

# Interesting things I have learned

- cvc5 has a dedicated theory of sets that builds on top of its SAT model for booleans, along with other potentially useful theories for the future
- zero arg rust closures look like a mis-placed logical or ||, weird
- Rc vs Arc differ due to thread safety, neither allow mutation those requrire Rc<RefCell<T>> or Arc<Mutex<T>>.
- There is Weak to solve cycles in Rc
- traits are like type classes
- they can be derived
- `#` is attribute, either built in or custom macros
- MACROS RULE!!!! Or, erm, `macro_rules!` lets you define some nice macros for code generation.
- The ! is for calling macros. ? is for monadic error handling (short circuits)
- send/sync traits control ability to transfer/share between threads, nice
- "arenas" allow lifetime to come together in blocks, sounds nice and efficient
- pub(crate) does the _opposite_ of what I suspected and it makes it crate-_only_ public, fun
- you have to "own" either the trait or the struct in order to impl
- ! is the Void type
- () is the unit type and unit value
- Box is for dynamic dispatch, e.g. `Box<dyn Animal>` for an Animal trait, gives you a vtable
- `::<...>` is a TURBOFISH!!!
- Rust distinguishes the use of `<>` better than C++ by requiring `::` in things like `Vec::<i32>`.
- Re-learned about phi nodes in SSA, that label the value taken based on where the execution path *came from*
- Learned about alloca and how a `mem2reg` optimization will often replace it with phi nodes etc
- Claude will often remove its own comments when editing sections of code. I'm not sure why it does this.
- I can viscerally feel the development process slowing down as the codebase grows. The changes are getting more complex, the amount of code that needs to change is growing, and unsurprisingly this means both Claude and I are beginning to make more mistakes and need more guidance and review.
- All the different theories that cvc5 supports, including "bags" as a name for multisets in the theory of bags
- LLVM supports arbitrary size integers out of the box, as long as their size is known at compile time
- Manually debugging a JIT is annoying, the backtrace is essentially useless!

# Things that surprised me

- How hard it is to stop typing "types" everywhere instead of sets etc.
- SMT solvers are branch heavy so aren't very SIMD/multi-thread friendly. Implication, I guess, is that we can at least try and run multiple solvers in parallel while compiling to make use of multi-threading in a simple way. Shame we can't just throw the problem at some beefy GPUs.
- How quickly the tree of language features to implement exploded! I seem to add about 5 new items into my to do list for every one I cross off!
- As I've been working with the LLMs to come up with the language it has ended being a lot more consistent and succinct than I expected.
- sonnet 4.6 seems to get itself tripped up by making assumptions a lot more than opus,
  and unfortunately they tend to compound: in future rounds it will read previous code and assume the prior assumptions
  to be valid. I've seen sonnet 5 do this less often so far, it appears to be better at noticing and raising issues - and recommends fixing them straight away more often.

# Open questions

- How to define exception handlers?

