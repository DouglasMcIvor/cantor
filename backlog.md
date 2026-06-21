This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do

- confirm that with constants I can declare my own compile time sets and use them as domains/ranges
- `distinct` and `alias` keywords as that combines nicely with the above
- function overloads, or as ChatGPT suggests "the language should officially define an overloaded function as *the union of compatible partial functions*". In my own words "all functions are partial until linking is complete"
- functions returning product sets
- CLI to output IR
- memory model
- ABI! (I just saw "// All function parameters are i64 (uniform ABI); widen Bool args." in the code, which is fine for now. Also needed to remove `FAIL_SENTINEL`)
- set comprehensions, including infinite generative sets
  - math syntax `{x*2 | x ∈ Nat, x > 0}` as sugar for the python form (deferred)
  - multi-binder `{x+y for x in A for y in B}` desugaring to Cartesian product (deferred)
- immutable set constants like `s = {1, 2, 3}`, need to be baked in as statics
- more basic values:
  - float
  - char, string (unicode I guess)
  - byte
- BigInt runtime support for our unsized Int and Nat sets
- constants JIT'd instead of at rust level to get consistency 
- spin up some code review agents to assess quality of rust implementation, factoring and maintainability before it gets too large
- human intros (familiar with types, newbie with the word type taboo'd) and LLM intro. The human intros would be good to include a bunch of Venn diagrams and ye olde curved arrows between ovals representing functions to visualise the concepts along the way.
- review and improve error messages
- suggested constraints in error messages
- more containers! gotta have me some vectors and maps, not just sets! ordered sets too
- iterators for containers 
- destructuring assignment and checks for values in product sets 
  ```haskell
  assert z in X * Y
  x, y = z
  assert x, y in X * Y
  ``` 
- natural `for i, x in foo` syntax to combine destructuring should fall out from the above without additional work
- outer IO loop
- write-only side effects via `emit`
- compiled binaries
- linker integration
- "named types" (Type vs NewType?) or whatever the thingy is called but in set language. I want to be able to make Litres that are numbers but form a distinct set.
- literal suffix support for e.g. 3m for 3 meters
- structs/"named product sets" and same for unions. product sets are either fully not named or fully named.
  Tentative syntax for products:
  ```
  Pair = distinct Meter * Meter
  mut p : Pair = (3m, 4m)

  Point = distinct (
      x: Meter
      y: Meter
  )
  mut p : Point = (
      x = 3m
      y = 4m
  )
  ```
  Tentative syntax for unions:
  ```
  Measurement = distinct Meter | Liter
  mut m1 : Measurement = 3m
  mut m2 : Measurement = 4l

  Measurement = distinct (
      Length: Meter
    | Volume: Liter
  )
  mut m1 : Measurement = Measurement.Length(3m) -- requires namespaces to exist first
  mut m2 = Measurement.Volume(4l) -- requires mutable range inference to exist first
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
- pattern matching with `match x { a => ... , b => ...}` or maybe
  ```
  speak :
    Dog   -> String
  | Cat   -> String
  | Table -> Error
  ```
- struct member functions?
- lambdas and closures
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
- automatic multithreading for semi-pure core?
- multiple concurrent IO threads?
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

# Things that surprised me

- How hard it is to stop typing "types" everywhere instead of sets etc.
- SMT solvers are branch heavy so aren't very SIMD/multi-thread friendly. Implication, I guess, is that we can at least try and run multiple solvers in parallel while compiling to make use of multi-threading in a simple way. Shame we can't just throw the problem at some beefy GPUs.
- How quickly the tree of language features to implement exploded! I seem to add about 5 new items into my to do list for every one I cross off!
- As I've been working with the LLMs to come up with the language it has ended being a lot more consistent and succinct than I expected.

# Open questions

- How should we implement built in containers like sets and so? Pull in a library or roll our own?
  - For temporaries: flat arrays to start to keep it simple, deallocate entire arena each IO loop, one arena to start
  - ChatGPT suggests `im` or `rpds` (its preference for some reason) for persistent data structures and eventually we can roll our own
- Should we represent values of lists of product sets automatically as a struct of arrays? That might be fun
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
- Does cvc5 come with a built-in timeout or limit for complex proofs? Should we let the user configure an "effort" value?
- Should we have an early `return` statement? Seems expected in imperative languages.
- How to define exception handlers?
- More generally, how to define the IO loop?
- Should we have a way to write programs without the IO loop runtime? If so how?

