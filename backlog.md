This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do

- runtime sets of course
- for over named sets not just set literals
- CLI to output IR
- memory model
- set comprehensions, including infinite generative sets
  - math syntax `{x*2 | x ∈ Nat, x > 0}` as sugar for the python form (deferred)
  - multi-binder `{x+y for x in A for y in B}` desugaring to Cartesian product (deferred)
- confirm that with constants I can declare my own compile time sets and use them as domains/ranges
- basic values that aren't int64:
  - bool
  - float
  - char, string (unicode I guess)
  - byte
- BigInt runtime support for our unsized Int and Nat sets
- constants JIT'd instead of at rust level to get consistency 
- spin up some code review agents to assess quality of rust implementation, factoring and maintainability before it gets too large
- human intros (familiar with types, newbie with the word type taboo'd) and LLM intro
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
- structs/"named product sets"
- struct member functions?
- lambdas and closures
- dynamic dispatch?
- macros. what is a natural Cantor way of doing code generation? functions that manipulate ASTs?
- generics. do we need mechanisms to help define functions that work on lots of different sets? seems like it should work alongside overloading

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
- Rust distinguishes the use of `<>` better than C++ by requiring `::` in things like `Vec::<i32>`.
- Re-learned about phi nodes in SSA, that label the value taken based on where the execution path *came from*
- Learned about alloca and how a `mem2reg` optimization will often replace it with phi nodes etc

# Things that surprised me

- How hard it is to stop typing "types" everywhere instead of sets etc.
- SMT solvers are branch heavy so aren't very SIMD/multi-thread friendly. Implication, I guess, is that we can at least try and run multiple solvers in parallel while compiling to make use of multi-threading in a simple way. Shame we can't just throw the problem at some beefy GPUs.
- 

# Open questions

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
- Should we use `:=` for mutable re-assignment to make it visually distinct from declaring a named value?
- Does cvc5 come with a built-in timeout or limit for complex proofs? Should we let the user configure an "effort" value?
- Should we have an early `return` statement? Seems expected in imperative languages.
- How to define exception handlers?
- More generally, how to define the IO loop?
- Should we have a way to write programs without the IO loop runtime? If so how?

