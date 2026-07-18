This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do
 
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
  `Measurement.length(3m)` construction — are DONE for Int-Kind-compatible arms, see
  README; a tuple/cross-kind arm like a hypothetical named-product arm still needs
  `distinct`'s Int-only basis assumption lifted, tracked separately)
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

