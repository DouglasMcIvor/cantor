This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do

- End goal: quantum paper bag using WASM and WebGL backend for Cantor
  (WASM half done — `examples/quantum_paper_bag.cantor` + `web/paper-bag.html`).
  Remaining:
  - The WebGL/WebGPU shader half is still open.
  - `acc ++ [x]` still allocates a one-element Arrow array per iteration —
    the loop-accumulator lowering (`src/codegen/accumulator.rs`) reuses
    `coerce_value_to_vector` to inherit its per-element tagging rules, and
    that path allocates per element. Pushing the single element straight
    onto the builder would remove it; the asymptotics are already fixed
    (O(1)-push builder), so this is just a constant factor.
  - The analysis is deliberately conservative: it bails on any read of the
    accumulator inside the nest, on a `return`, and on nested-loop
    re-entry. `for ... in` loops are not covered yet, only `while`.
- **`quot`/`rem` are unavailable in more places than expected.** They only
  codegen inside an Int64-promoted function, and promotion additionally
  requires the *range* to be an integer — a `-> Bool` predicate that wants
  `rem` silently can't have it, and has to return 1/0 instead. Also
  observed while writing the paper bag: routing an operand through
  `clamp32` immediately before the `quot` loses the promotion, while a
  guard proving the same bound keeps it. Not root-caused; worth a look
  since the workaround is non-obvious and the error message ("not proven to
  fit Int64") points at the value rather than at the promotion.
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
- `check pred(x) for x in X` keyword for property based testing, unit testing as the degenerate case. 
  Sits between `assert` and `require` in strength. 
  Maybe `check ... and assert` for another variation.
- abduction driven testing! use the suggested constraints to inform the cases that check looks at
- path driven fuzzing as well, like afl
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
  - `Float64` as a distinct set (`Float32`/`FiniteFloat32` DONE 2026-08-29:
    lexing, parsing, Kind inference, cvc5 FloatingPoint encoding, LLVM f32
    codegen). Also still need raw decimal literals like `3.14` (currently
    no float literal syntax at all) and explicit `posZero`/`negZero`/`nan`
    values.
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
- operator overloading for things like `List(Byte)`?
  - custom operator overloading syntax like with haskell? I don't care for inventing new ops but supporting existing ones might be important
  - automatic operator overloading for disinct sets, like allowing arithmetic on Litre. See `deriving` below.
- constants JIT'd instead of at rust level to get consistency 
- human intros (familiar with types, newbie with the word type taboo'd) and LLM intro. The human intros would be good to include a bunch of Venn diagrams and ye olde curved arrows between ovals representing functions to visualise the concepts along the way.
- error messages
  - review and improve error messages
  - suggested constraints in error messages. **Use abduction, not the unsat
    core** (design-decisions.md §1 said unsat core; corrected 2026-07-27).
    The proof query asserts the domain constraints plus the *negation* of the
    range obligation, so a failed check comes back `sat` — there is no unsat
    core in exactly the case where the user needs a suggestion. cvc5's
    `get_abduct` (`cvc5-0.4.0/src/solver.rs:653`) solves the right problem
    directly: find ψ with `domain ∧ ψ ⊨ goal`. Use the grammar-constrained
    variant (same `Grammar` type as the SyGuS bindings below) so every
    suggestion is expressible in Cantor syntax — unrestricted abduction will
    happily return the goal itself. Spike it standalone against the `cvc5`
    crate first, the way `nl-cov` was validated in
    docs/int-soundness-review-2026-07-05.md; performance in our setting is
    unknown. Runs on the error path only, behind the usual `--timeout`.
  - **unsat core has its own, different feature**: on a check that *succeeded*,
    the core says which domain hypotheses were actually needed — so it can
    report over-constrained signatures ("declared `NatPos`, proof only used
    `x >= 0`"). Worth doing, but it is not the suggested-constraints feature.
  - **static "roof" diagnostics** — some obligations are in fragments with no
    decision procedure, and today they present as an indefinite hang rather
    than a result (cvc5's `tlimit` is advisory; the Kleene-star fixture blows
    past the 60s default, and the `x*x` review measured `tlimit=5000` ignored
    outright). Detect the known-unanswerable shapes *before* calling cvc5 and
    report a specific `Unknown` with a concrete fix. The main one today:
    a quantified sequence-membership obligation combined with a loop
    inductive step. Note the quantifier comes from the element set having a
    scalar constraint — `Nat*` emits `∀i. out[i] >= 0`, whereas `Int*`,
    `Char*` and `Bool*` are `Membership::Unconstrained` and emit no
    quantifier at all, so "use `Int*` and assert non-negativity where the
    elements are consumed" is a real, checkable suggestion no solver could
    produce (it never returns). See
    `tests/solver/vectors.rs:539`'s ignored fixture and
    design-decisions.md's Kleene-star note.
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
  Tree = distinct (Leaf: Int | Node: (Tree * Tree))

  area(Shape.Circle(r)) = r * r        -- DONE
  area(Shape.Rect(x, y)) = x * y       -- DONE (tuple arm destructures)
  ```
  **DONE** for non-recursive named unions where the argument's arm is statically
  visible at the call site (commit `4c04957`, pattern-matching plan step 4/4).
  User-facing writeup is in README.md ("Constructor patterns"), *not*
  design-decisions.md — the latter only covers the labeled-arm tag-forcing
  prerequisite. Tests: `tests/{solver,cli}/constructor_patterns.rs`.
  Design notes live in the commit message; what follows is only what's left.

  Remaining work, in rough priority order:

  - **`==`/`!=` on two `Kind::TaggedUnion` values is unsound at codegen** — still
    live (`Shape.Circle(3) != Shape.Radius(3)` is solver-proved true, runs as
    `false`). `codegen::expr::compile_binop`'s generic path calls
    `narrow_tagged_union`, which drops the tag and compares payload only. Old
    general code, but only *reachable* since labeled constructors let a user force
    two overlapping same-Kind arms. Fix is either (a) tag-first compare with a
    per-arm branch over the active arm's own leaves (mirror `codegen::show`'s
    dispatch — avoids comparing `undef` trailing leaf slots), or (b) zero-fill
    unused leaves at every `TaggedUnion` construction site so a whole-struct
    compare is safe. Worked around in the suite by never comparing these values
    (`tests/cantor_files/named_union_shape.cantor`).

  - **Indirect calls stay `Unknown`/counterexample** — `area(pick(b))`, where
    `pick`'s returned arm isn't visible at the call site. Needs a cross-function
    fact ("any `Shape` tagged `Circle` has a payload in `Nat`") for an *opaque*
    term. **Dead end, do not retry as-is**: asserting it as a per-arm `Forall` over
    the union's datatype sort made cvc5 report the entire assertion set as
    inconsistent — a claim *and* its negation both came back "Proved". Reproduced
    minimally against the `cvc5` crate directly with no Cantor code, independent of
    `mbqi`/`nl-cov`/timeout. Strictly worse than the gap it closes, so it was
    reverted. Worth retrying on a newer cvc5, or reshaping as a ground per-call
    obligation threaded through call contracts (a real solver-architecture change).

  - **Recursive named unions** (`Node: Tree * Tree`) are blocked on
    docs/recursive-sets-plan.md phases 1-3, not on anything pattern-specific.

  - **Arm narrowing after `from()`** (`from(Shape.Rect((3,4))).0`) isn't provable —
    pre-existing and not `distinct`-specific (the plain `(Nat*Nat) | Nat` version
    fails identically), so it's tracked with cross-kind unions rather than here.
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
  **In progress (v0, no closures/lambdas yet):** `->` now parses as a real,
  right-associative operator anywhere it's explicitly parenthesized
  (`(Int -> Int) * Int -> Int`, and `(A -> B -> C)` right-associates) —
  `parser::expr`'s `LParen` arm, the only place it nests; the bare top-level
  `name : domain -> range` split is untouched. `Kind::Function(domain,
  range)` exists, stored as a plain i64 function pointer, reusing all the
  scalar-Kind wire plumbing. A bare reference to a **non-overloaded**
  top-level function name elaborates as a value of that Kind
  (`semantics::elaborate::expr`'s `Var` fallback, after locals/name_defs);
  an overloaded name is a clear `Unsupported` error, not a crash — no single
  LLVM entry point exists for it yet (planned next: synthesize one, a
  runtime-dispatch wrapper reusing `codegen::overload_dispatch`'s existing
  logic). Calling through a function-Kind local/param routes by an
  env-first lookup in `Call` elaboration (mirroring `Var`'s own
  locals-shadow-everything priority) and exact-Kind-checks the argument
  (`CompileError::FunctionValueArgKindMismatch` on mismatch) — no coercion
  story for function values yet.
  **Solver, body-side domain proof: DONE.** A call `f(x)` inside the body of
  the function that declared `f : (Int -> Int)` is now genuinely proved (or
  disproved with a real counterexample), not just Kind-checked — the
  enclosing signature's own declared domain/range for `f` (an
  `EncodeCtx::param_domain_exprs` map, seeded once per function-check from
  `sem_param_set_exprs`/`domain_parts`, threaded through `LoopCtx` too for
  calls inside loop bodies) is reused as a synthesized single-signature
  `SemFunctionSig`, feeding the *same* `sig_domain_match`/
  `assert_call_contract` machinery an ordinary named call already uses
  (`solver::encode_hof::encode_function_value_call`, split into its own
  file to keep `encode_call.rs` under the repo's line-count guideline).
  `apply : (Int -> Int) * Int -> Int / apply(f, x) = f(x)` now reports
  `proved`; a narrower declared domain (e.g. `f : NatPos -> Int` called with
  an unconstrained `Int` `x`) reports a real counterexample. `f`'s own
  parameter binding needed a placeholder fix too: `sig_check::
  build_param_terms` unconditionally tried to build a CVC5 constant for
  every parameter, including function-Kind ones, which have no sort — now
  an unconstrained fresh Boolean placeholder (never semantically read; a
  call through it resolves by *name*, not by its term value). Along the
  way, found and fixed a real, separate bug this surfaced:
  `semantics::elaborate::binop`'s generic comparisons/logical catch-all
  silently handled `BinOp::Arrow` too (no dedicated arm existed) and
  hardcoded `kind_of: Kind::Bool` for every `Domain -> Range` sub-
  expression — invisible to every prior test (all exercised `kind::
  set_kind` directly or `Ctx::fn_sigs`'s separately-computed `param_kinds`,
  never a function's own *elaborated* `sigs[0].domain`), caught only via
  the solver reporting "unsupported domain sort" on `apply`'s own domain
  annotation. Now a dedicated arm, Set-position only, matching `Union`/
  `Intersect`/`SymDiff`'s existing shape.
  **Still not done — call-site check:** a *caller* passing a concrete
  function in (`apply(double, 5)`) isn't solver-encodable yet
  (`Kind::Function` has no CVC5 sort), so that call site still reports a
  clean `unknown` ("unbound variable `double`") — independently of the
  body-side proof above, so no false `proved` results from this gap. Per
  the user's explicit choice (2026-08-29 design discussion): when a
  function-value argument becomes encodable, close this with an **exact
  structural Set match** (not real variance/subtyping — deliberately out of
  scope, avoids new solver machinery) between the passed function's own
  declared domain/range and the parameter's declared `arrow`, comparing
  `ast::Expr`s span-insensitively (no such comparator exists yet — `Expr`/
  `ExprKind` don't derive `PartialEq`). Also open: the counterexample
  witness line prints the function-Kind placeholder as `f = false` (cosmetic
  — the Boolean placeholder has no real decode path, not a soundness issue).
  **Codegen: DONE.** A bare function reference compiles to that function's
  address (`ptrtoint`); calling through a function-Kind local/param compiles
  to a genuine indirect call (`inttoptr` + `build_indirect_call`,
  `codegen::expr_call::compile_indirect_call`) — verified by actually
  JIT-executing (not just inspecting IR), including a two-function case that
  confirms the indirect call dispatches to whichever address was actually
  passed, and a `mut g : (Int -> Int) = double` local. Since `cantor run`
  requires a full proof first and this shape is still solver-`unknown` (see
  above), these run via `compile_file` (the unverified/no-solver path
  `tests/codegen` already uses for other JIT fixtures), not the CLI —
  `tests/codegen/higher_order_functions.rs`.
  **Domain-representation ambiguity: FIXED.** `Kind::Function` now stores
  the domain as `Vec<Kind>` — the flat per-parameter list, matching
  `codegen::declare_function`'s own `param_kinds: &[Kind]` shape — instead
  of a single, sometimes-collapsed-into-`Tuple` Kind. This closed a real
  latent hazard, not just a cosmetic one: a function with *one* tuple-typed
  parameter (`pair_sum : (Int * Int) -> Int`, real LLVM ABI = one struct
  argument) used to be *indistinguishable* at the Kind level from a
  *two*-scalar-parameter function of the same element Kinds (`add2 : Int *
  Int -> Int`, real ABI = two i64 arguments) — both collapsed to the same
  `Kind::Function` domain, so nothing would have stopped a caller from
  passing `pair_sum` somewhere `add2`'s shape was expected and calling it
  with 2 separate args, building an indirect-call function type that
  doesn't match the real callee's LLVM signature (a genuine ABI mismatch —
  undefined behaviour at runtime, not just a wrong answer). Now
  `vec![Tuple([Int, Int])]` (arity 1) and `vec![Int, Int]` (arity 2) are
  distinct, and `compile_indirect_call` just uses the declared list
  directly — no more `args.len() > 1` inference. An inline `Domain ->
  Range` Kind annotation (`set_kind`'s `Arrow` arm) always flattens `*`
  into separate params via `flatten_domain` (same as an ordinary function's
  own domain) — so a one-tuple-param function like `pair_sum` still can't
  be *declared into* a function-Kind parameter today (no syntax expresses
  that shape), a real but narrow, honestly-scoped gap:
  `tests/semantics/higher_order_functions.rs`'s
  `single_tuple_param_function_has_a_different_domain_from_two_scalar_params`
  pins the Kind distinction directly since no full program can exercise it
  end-to-end yet.
  **Still open:** overloaded names as values (synthesized runtime-dispatch
  wrapper, see above) is the agreed next step, then `>>` composition
  (design-decisions.md §10).
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

