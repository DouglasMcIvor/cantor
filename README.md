# Cantor - ℵ

![Cantor programming language logo](docs/cantor_logo.png)

> *A statically typed language without any types.*

Named after [Georg Cantor](https://en.wikipedia.org/wiki/Georg_Cantor), the mathematician who built the foundations of modern set theory.

## The idea

Most programming languages are built on type theory.
Most of mathematics is built on set theory.

Type theory was introduced into the foundations of mathematics largely to sidestep problems with infinite sets — most famously Russell's paradox, which arises when you let a set contain itself.
But programmers never actually need infinite sets.
A computer is a finite state machine; it only approximates a Turing machine until it runs out of RAM.
The sets a programmer cares about — integers that fit in 64 bits, HTTP status codes, non-negative numbers — are all finite.

So: if applied mathematics doesn't require type theory to get things done, and if the specific problem type theory was introduced to solve (infinite self-referential sets) never arises in practice, then maybe applied programming doesn't need types either.

Cantor is a fun (at least, _some people_ find it fun) experiment in that direction.
Instead of a type system, functions declare their **domain** and **range** as sets.
The compiler uses an SMT solver to *prove* that every possible input satisfying the domain maps to an output in the range.
If it can't prove it, it shows you a concrete counterexample.

```haskell
abs : Int -> Nat        -- for ALL integers x, abs(x) is a natural number
abs(x) = if x >= 0 then x else -x
```

The compiler doesn't check a type annotation — it proves the claim.

The seed for this was Evan Jenkins's 2014 post
[*Why Dependently Typed Programming Will (One Day) Rock Your World*](http://ejenk.com/blog/why-dependently-typed-programming-will-one-day-rock-your-world.html).
Jenkins works through three solutions to the divide-by-zero problem.
The third — and best — looks roughly like:

```c
float myDivide3(float a, float b, proof(b != 0) p) {
    return a / b;
}
```

The insight is that you make the *caller* prove that `b` is non-zero.
In Jenkins' words: 

> If you can't justify why the divisor isn't zero, you have no business dividing.

Jenkins's conclusion points to [Idris](https://www.idris-lang.org/), a dependently-typed language where those proofs are encoded in the type system.

Cantor goes somewhere different (and I suspect contradicts some of [the spirit](https://qchu.wordpress.com/2013/05/28/the-type-system-of-mathematics/) of what Jenkins is aiming for!).
Rather than encoding proofs as types (which requires a rich type system), Cantor asks: what if there were no type system at all, just sets?
And rather than making the programmer supply the proof, Cantor's compiler finds it automatically — it hands the constraint to an SMT solver and either gets a proof back, or gets a concrete counterexample showing exactly where the claim fails.

The result is a language where `safe_div : Int * (Int - {0}) -> Int` is not a type annotation but a *theorem*, and the compiler either proves it or shows you the input that breaks it.

Of course, nothing in the world is free. The trade off we expect to make here is:

* Complex claims can take a *really* long time to prove. SAT is infamously NP-complete.
* ...so we should expect to need a *lot* of `assert`s. The simplest way to provide a proof? Tell the compiler what to do when it's false!

But there are some really good SAT solvers out there, so maybe we can get away without needing "asserts where it hurts"?

Ultimately the goal of abandoning types is to make programming simpler. The beauty of Lisp with its homoiconic macros is that metaprogramming and programming both share the same mental model, so your cognitive load is lower. C++ on the hand is famously 4 languages in one: C, object-oriented C++, templates and the functional-style algorithms from the standard library. The hope for Cantor is that if you don't even need to distinguish between _types_ and _values_ then maybe some nice simple consequences will fall out from the design down the road.

While Lisp is homoiconic, Cantor is _homovalent_ - same valued.

## How it works

Every function signature is a mathematical claim: *for all inputs in the domain, the output is in the range.*
The compiler encodes this as a constraint-satisfaction problem and hands it to [cvc5](https://cvc5.github.io/), a state-of-the-art SMT solver.
Every check has one of three outcomes:

| Outcome | Meaning |
|---|---|
| `proved` | The solver confirmed the claim holds for every possible input. |
| `counterexample` | The solver found specific values that violate the claim, shown in the output. |
| `unknown` | The claim couldn't be decided statically — if you provide an `assert` then a runtime check is emitted instead. |

`proved` is the goal.
`counterexample` is a bug report with a witness.
`unknown` is honest: the compiler tells you what it couldn't verify, and gives you the option of letting the program still run with a runtime guard in place.

## Examples

### Basic proof

```haskell
abs : Int -> Nat
abs(x) = if x >= 0 then x else -x
```

```sh
$ cantor abs.cantor
  proved          abs : Int -> Nat

  1 proved, 0 counterexample(s), 0 unknown
```

### Division safety

The domain `Int - {0}` (integers minus zero) excludes the one input that would cause undefined behaviour.
The compiler proves the exclusion is respected at every call site.

```haskell
safe_div : Int * (Int - {0}) -> Int
safe_div(x, y) = x / y
```

```sh
$ cantor safe_div.cantor
  proved          safe_div : Int * (Int - {0}) -> Int
```

### Counterexample

```haskell
broken : Nat -> Int16
broken(x) = x * 1000
```

```sh
$ cantor broken.cantor
  counterexample  broken : Nat -> Int16
    x = 33  ->  output = 33000  (not in Int16)
```

The solver found that `x = 33` produces `33000`, which overflows a 16-bit integer.

### Constants

Constants are compile-time values, type-checked against their declared set.
They are automatically inlined everywhere they are used.

```haskell
scale : Nat
scale = 1000

pi_scaled : Nat
pi_scaled = 3 * scale + 141

circumference : Nat -> Nat
circumference(r) = 2 * pi_scaled * r / scale
```

### Error handling with `Fail`

`Fail` is a built-in set used as a failure sentinel.
A function that might fail declares `Fail` in its range.
The `?` operator propagates failure up to the caller (which must also declare `Fail`).

```haskell
safe_to_nat : Int -> Nat | Fail
safe_to_nat(n) {
    assert n in Nat    -- proved statically if possible; runtime check otherwise
    n
}

add_positive : Int * Int -> Nat | Fail
add_positive(x, y) {
    mut a: Nat = safe_to_nat(x)?
    mut b: Nat = safe_to_nat(y)?
    a + b
}
```

The compiler proves that when neither `safe_to_nat` call fails, `a + b` is in `Nat`.

### Helping the compiler out (or lying to it): `assert`, `require` and `assume`

```haskell
clamp : Int * Nat * NatPos -> Nat
clamp(x, lo, hi) {
    assert lo < hi        -- runtime check: caller's responsibility
    assume x >= 0         -- escape hatch: "trust me, I know the caller"
    if x < lo then lo else if x > hi then hi else x
}
```

`require` is a compile-time proof obligation — a hard error if it can't be proved.
`assert` graduates: if provable, it's elided; if always false, it's a compile error; if unknown, it becomes a runtime check.
`assume` is an escape hatch: "honest guv! the solver can't see this but I just know it's true!"

### Loops and loop invariants

`while` loops use `mut name: Set = expr` to declare both a mutable local and its **loop invariant** — the set the variable must remain in across every iteration.

```haskell
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0   -- 0 ∈ Nat ✓  (init); Nat is the invariant for acc
    mut i: Nat = 1     -- 1 ∈ Nat ✓  (init)
    while i <= n {
        acc = acc + i  -- acc + i ∈ Nat asserted (step: trusted, see below)
        i = i + 1      -- i + 1 ∈ Nat asserted (step: trusted)
    }
    acc                -- acc ∈ Nat from invariant + ¬(i <= n) → ℵ proved
}
```

```sh
$ cantor sum_to.cantor
  ℵ proved   sum_to : Nat -> Nat
```

The declared constraint is used in three places: the initial value is checked against it, each assignment asserts the new value satisfies it, and after the loop the post-loop SSA variable inherits it as a known fact.

> **Note — the compiler verifies the inductive step.**
> Before trusting the invariant for post-loop reasoning, the solver checks that one body iteration actually maintains it: given `acc ∈ Nat` and the loop condition, does `acc = acc + i` leave `acc` still in `Nat`?
> If the step cannot be proved — for example, `mut acc: Int16 = 0` with `acc = acc + 1` in an unbounded loop — the compiler reports a counterexample immediately rather than a false `proved`.
> Loop variables declared as `mut name: Int` carry no effective constraint (Int = all integers) and behave conservatively: if the range obligation depends on such a variable, the result is `unknown` rather than a potentially spurious counterexample.

### For-in loops

`for x in S` iterates over a set literal, binding `x` to each element in turn.
The same loop invariant mechanism applies: `mut acc: Set` declares the invariant, and the compiler verifies it is maintained across every element.

```haskell
sum_set : -> Nat
sum_set() {
    mut acc: Nat = 0
    for x in {1, 2, 3} {
        acc = acc + x
    }
    acc      -- acc ∈ Nat proved inductively over all elements
}
```

Naming the loop variable with an uppercase letter (`for X in {1, 2, 3}`) promises that the value is known at compile time and forces the compiler to verify the iterable is statically materializable — a lightweight way to opt into guaranteed compile-time unrolling.

### Set comprehensions

`{ expr for x in S if pred(x) }` produces a new set by mapping and filtering an existing one.
Comprehensions work anywhere a set expression is valid: domain and range annotations, `in`/`not in` predicates, and as the source of a `for` loop.

```haskell
-- Domain annotation: only integers greater than 5
f : {x for x in Nat if x > 5} -> NatPos
f(n) = n

-- As a for-in source: sum of doubled odd elements
sum_doubled_odds : -> Nat
sum_doubled_odds() {
    mut acc: Nat = 0
    for y in {x * 2 for x in {1, 2, 3, 4, 5} if x mod 2 != 0} {
        acc = acc + y
    }
    acc      -- 2 + 6 + 10 = 18
}
```

The source set can be a finite literal (unrolled statically) or an infinite named set like `Nat` (encoded as an SMT predicate).
Captured runtime variables work in both the output expression and the filter:

```haskell
sum_above_threshold : Int -> Int
sum_above_threshold(threshold) {
    mut acc: Int = 0
    for y in {x for x in {10, 20, 30, 40} if x > threshold} {
        acc = acc + y
    }
    acc
}
```

## Features (working today)

- **Set-theoretic domains and ranges** — `Int`, `Nat`, `NatPos`, `NonZeroInt`, `Int8`–`Int64`, set literals `{0, 1, 2}`, set difference `A - B`, union `A | B`, intersection `A & B`
- **Set comprehensions** — `{ expr for x in S if pred(x) }` in domain/range/`in`/`for` positions; finite literal sources unrolled statically; infinite named sources encoded as SMT predicates
- **SMT-backed proof** — every function signature is proved, disproved (with a counterexample), or flagged unknown using cvc5
- **Interprocedural checking** — callee contracts are used modularly; recursion works via the function's own signature as an induction hypothesis
- **Constants** — `name : Set / name = expr`, type-checked and auto-inlined at compile time
- **Block bodies with `while` and `for x in S` loops** — imperative-style bodies with `while cond { stmts }` and `for x in {e1, e2, …} { stmts }`, `mut name: Set = expr` locals (set annotation is the declared loop invariant), sequenced statements, and `if-then-else`
- **`require` / `assert` / `assume`** — static and graduated runtime proof obligations
- **`Fail` and `?`** — monadic error propagation; fallible functions declare `| Fail` in their range; `?` short-circuits on failure
- **Named set naming convention** — uppercase names are compile-time set names (`Nat`, `HTTPError`); lowercase names are values (`pi`, `abs`, `collected_primes`); enforced by the compiler
- **JIT execution** — `cantor run <file>` checks proofs then JIT-compiles and runs `main` via LLVM

## On the roadmap

- **Runtime sets** — sets as first-class runtime values; `collected_primes` as a real set you can iterate, test membership, and pass around; comprehensions that produce a set value rather than being unrolled statically
- **Named error sets** — `HTTPError = {400, 503}`; `fetch : Request -> Response | HTTPError`; richer than `Fail` without any new language mechanism
- **User-defined named sets** — `EvenNat = { n in Nat | n mod 2 == 0 }` as a top-level definition
- **`raise` and `emits`** — unrecoverable errors and write-only side effects (logging, metrics)
- **State** — mutable program state that survives between calls, with a proof that it satisfies its invariants at every boundary
- **Module system** — imports, library compilation, separate checking

## Are you serious!?

No. This is not a serious language. I built it for fun and to learn Rust.

That said, many good things in the world have come from people being simply curious, wanting to explore an idea, and enjoying the journey for its own sake.
The question "what if we threw out the type system and only kept sets?" is fun to explore, and working through the answers — even in prototype form — has taught me a lot about SMT solvers, LLVM, and language design.

I would have done it _years_ ago (the inspiration was back in 2014 after all!), but until our silicon friends showed up and could help me out it had seemed like a vast and daunting prospect to attempt.

If you find any of it interesting or want to argue about ~type~ set theory, feel free to fork or open an issue!

## Building

Dependencies:

- Rust (edition 2024)
- LLVM 18 (`llvm-18-dev` on Debian/Ubuntu)
- cvc5 (`libcvc5-dev` on Debian/Ubuntu)

```
cargo build
cargo test
cargo run -- <file.cantor>          # check proofs
cargo run -- run <file.cantor>      # check then JIT-run main()
```
