This is my personal backlog/random things I've learned or want to remember.
You probably don't want to read this unless you're me.

# To do

imperative blocks
assume/require
monadic errors
assert
loops
outer IO loop
compiled binaries
linker integration
README with examples, human intro and LLM intro
constants

# To learn

- Actually write some rust by hand, old skool
- Haha, even funnier: actually run the _build command_ by hand!
- What does .into() do?

# Interesting things I have learned

- cvc5 has a dedicated theory of sets that builds on top of its SAT model for booleans, along with other potentially useful theories for the future
- zero arg rust closures look like a mis-placed logical or ||, weird
- Rc vs Arc differ due to thread safety, neither allow mutation those requrire Rc<RefCell<T>> or Arc<Mutex<T>>.
- There is Weak to solve cycles in Rc
- traits are like type classes
- they can be derived
- # is attribute, either built in or custom macros
- MACROS RULE!!!! Or, erm, `macro_rules!` lets you define some nice macros for code generation.
- The ! is for calling macros. ? is for monadic error handling (short circuits)
- send/sync traits control ability to transfer/share between threads, nice
- "arenas" allow lifetime to come together in blocks, sounds nice and efficient
- pub(crate) does the _opposite_ of what I suspected and it makes it crate-_only_ public, fun
- you have to "own" either the trait or the struct in order to impl
- ! is the Void type
- () is the unit type and unit value
- Box is for dynamic dispatch, e.g. `Box<dyn Animal>` for an Animal trait, gives you a vtable


# Things that surprised me



# Open questions

- How to define exception handlers?
- More generally, how to define the IO loop?
- Should we have a way to write programs without the IO loop runtime? If so how?
