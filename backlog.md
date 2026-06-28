This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do

- should `len` be replaced with just `size`? any other built in functions I need?
- `none` value and `None` set, currently missing
- function overloads, or as ChatGPT suggests "the language should officially define an overloaded
  function as *the union of compatible partial functions*". In my own words "all functions are partial
  until linking is complete"
- see if we can switch to proper ListArrays for nested vecs instead of using pointers? Or perhaps the current approach 
  is better for mutability etc?
- CLI to output IR
- more set comprehensions features
  - math syntax `{x*2 | x ∈ Nat, x > 0}` as sugar for the python form (deferred)
  - multi-binder `{x+y for x in A for y in B}` desugaring to Cartesian product (deferred)
- immutable set constants like `s = {1, 2, 3}`, need to be baked in as statics
- value literals desugaring in compile time set positions and support for sequences of literal values.
  E.g.
  - `Nat* - {}` (prefer over the empty set interpretation as that's _useless_)
  - `Nat* - {[]}`
  - more ambitiously `Nat* - {4}`/`Nat* - {[4]}`/`Nat* - {(4)}` as all equivalent!
    "My vector can be anything except a length 1 list containing a 4".
    I don't expect the solver to work very well in the last case, but we should at least
    let the user try and write it.
- more basic values:
  - `Int32`, `Int(32)` and their Nat cousins as LLVM iN values, right now all are i64. Rely on the optimizer to pack or not etc.
  - `Float32` and `Float64` as distinct sets, `FiniteFloat32` and explicit `posZero`, `negZero`, `nan` values
  - `Signed32`, `Unsigned32` etc for wrapping arithmetic distinct from `Int` and `Nat`
  - `Char` (unicode), our string type is `Char*` which is just too perfect to be true.
  - `Byte`, `Bits32`, `Bits(435)` generic etc
  - `Size`, `Word` (platform dependent)
- more containers:
  - maps
  - ordered sets
  - deques and stuff like that?
- more operators:
  - quot and rem (instead of modulo)
  - bitwise ops on bytes
  - comparison operators (they are in the lexer but I don't think they are implemented)
- `Rational` support, including making `/` for `Int` return `Rational`
  - adding `quot` and `rem` to keep `Int` inside `Int`
- operator overloading for things like `List(Byte)`?
  - custom operator overloading syntax like with haskell? I don't care for inventing new ops but supporting existing ones might be important
  - automatic operator overloading for disinct sets, like allowing arithmetic on Litre. See `deriving` below.
- Use `iN` in the LLVM IR for `Int(N)` and cousins, i.e. whenever the size is known at compile time.
- BigInt runtime support for our unsized `Int` and `Nat` sets, should come after function overloading so that
  ```
  foo : Int -> Int
  ```
  gets compiled into an `Int64` overload and a `BigInt = Int - Int64` overload. That way if someone writes a main
  that verifies input is within a reasonable range they should never need to link the big int library.
  `BigInt` is platform dependent, it just means "can't fit into a machine word" so
  ```
  require x not in BigInt
  assert x not in BigInt
  ```
  becomes useful for optimization without needing to know about the target architecture.
  ChatGPT suggests num-bigint as a mature widely used pure rust impl.
- constants JIT'd instead of at rust level to get consistency 
- spin up some code review agents to assess quality of rust implementation, factoring and maintainability before it gets too large
- human intros (familiar with types, newbie with the word type taboo'd) and LLM intro. The human intros would be good to include a bunch of Venn diagrams and ye olde curved arrows between ovals representing functions to visualise the concepts along the way.
- error messages
  - review and improve error messages
  - suggested constraints in error messages
  - counterexample printing TODOs
- recursive set definitions:
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
- should we use apache arrow for runtime storage of containers so that we serialisation for free? gives us struct of arrays naturally too
  * vector → balanced tree of chunks
  * set → hash table of chunks
  * map → hash table of key/value chunks
  * string → rope of UTF-8 chunks
  But the leaf representation is always the same immutable Arrow arrays.
- natural `for i, x in foo` syntax to combine destructuring should fall out from the above without additional work
- destructuring assignment should work when we "don't provide enough binders" so that
  ```
  x, y = (1, 2, 3)

  x = 1
  y = (2, 3)
  ```
  are equivalent, without needing cons lists. The rule is simply "tail goes into the last binder".
- could also add: tuple-level constraint `x, y : Int * Nat = ...`; nested patterns; `_` wildcard; per-binding mutability
- allow overloading with literals, like `factorial(0) = 1` as sugar for the domain being `{0}`
- nice syntax for guards, e.g.
  ```
  sign(x) | x < 0 = -1
  sign(0)         = 0
  sign(x)         = 1
  ```
  clearly needs just one domain and range declaration then the equivalent might be
  ```
  sign(x : {x for x < 0}) = -x
  ```
  so the sugar is
  ```
  sign(x for x < 0) -x
  ```
  which is lovely
  impl again as overloading on distinct domains
- along with recursive set definitions we get should allow constructors in binders
  ```
  Tree = leaf: Int | leaf2: (X * Y) | node: (Tree * Tree)

  size(x, y : X, Y) = ...
  size(Tree.leaf2(x, y)) = ..
  ```
- outer IO loop
  - allow different Output sets, can write pure cantor transformers from one Output to another
  - eventually lots of different output backends: CLI, TUI, web, SDL, OpenGL, vulkan, etc.
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
- structs/"named product sets" and same for unions. product sets are either fully not named or fully named.
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
  Tentative syntax for unions:
  ```
  Measurement = distinct Meter | Liter
  mut m1 : Measurement = 3m
  mut m2 : Measurement = 4l

  Measurement = distinct (
      length: Meter
    | volume: Liter
  )
  mut m1 : Measurement = Measurement.length(3m) -- requires namespaces to exist first
  mut m2 = Measurement.volume(4l) -- requires mutable range inference to exist first
  ```
  ChatGPT likes it:
  > For named products, field names feel like named projection functions. p.x is shorthand for applying the projection corresponding to the x component.
  >
  > For named unions, constructor names feel like named injection functions. Result.Ok(3m) is shorthand for applying the canonical injection from Meter into the Result union.
  >
  > Those are exactly the two fundamental morphisms associated with products and coproducts in category theory:
  >
  > Products have projections.
  > Coproducts (unions) have injections.
  >
  > You don't need to mention category theory anywhere in the language documentation, of course, but it's a reassuring sign. When the syntax naturally lines up with deep mathematical structures, it usually means you've found something that will remain coherent as the language grows. In Cantor, . naturally denotes projection (p.x), and Constructor(...) naturally denotes injection (Result.Ok(3m)). That symmetry feels remarkably elegant.
- mutable range inference
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
- dynamic dispatch? - this is just overloading a function to get a union domain and the compiler outputting a switch or a jump table!
- macros. what is a natural Cantor way of doing code generation? functions that manipulate ASTs?
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
- automatic multithreading for semi-pure core?
- multiple concurrent IO threads? ChatGPT convo suggests developing a _scheduler_ using optimisitic concurrency control, taking adaptive measurements on which events conflicts, both statically and dynamically determining state partitions for different event handlers, letting the developer declare that events are `ordered` or `unordered` or `mostly independent` so that we know the "shape" of events. Lots of fun stuff we could do!
- small runtime sets optimized as bitmasks. Once we get to the homogeneous set level the runtime doesn't actually care what the values are. So a cardinality 64 set can be encoded as just a uint64. It may make sense to extend this to fairly large sets with vectors of uint64. It would be nice to benchmark when this breaks down (time space tradeoff right?)
- Optimizations! From ChatGPT:
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

- Actually write some rust by hand, old skool
- Haha, even funnier: actually run the _build command_ by hand!

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

# Open questions

- Does all of overloading, generics and dynamic dispatch collapse into the one thing? Either the compiler proves a particular definition is used or else it outputs a vtable?
- I wanted 'emit' for write only effects, but when we added multithreading we will need synchronoisation. Is that a problem?
I guess it depends on how we handle threading.
- Memory model - leaning toward (from ChatGPT):
  ```
  persistent structures
    ->
  sharing
    ->
  cheap diffing
    ->
  easy reclamation
  ```
  The persistent state can use tracing GC _during the diff_. This is also simultaneous with IO so can naturally run in parallel.
  The only gap left is that the mutable arena could grow too large. Later on we could add pages to the arena to allow partial clean up like with tcmalloc and marking the pages available to the OS!
- How to define exception handlers?
- More generally, how to define the IO loop?
- Should we have a way to write programs without the IO loop runtime? If so how?

