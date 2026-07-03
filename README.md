# Cantor - ℵ

![Cantor programming language logo](docs/cantor_logo.png)

> *A statically typed language without any types - values are all you need!*

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

Every function signature is a mathematical claim: *for every input in the domain, whenever the function returns, its output is in the range.*
The "whenever it returns" matters: Cantor proves *partial* correctness — a function that never terminates satisfies any range vacuously, and termination checking is a separate (deferred) feature.
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

> **Known unsoundness (v0):** the solver reasons in unbounded ℤ, but the runtime
> currently stores every integer in a 64-bit machine word. A claim like
> `f : Int * Int -> Int` with `f(x, y) = x * y` is proved mathematically, yet the
> JIT wraps silently past ±2⁶³ — so a proved theorem can be visibly false at
> runtime near the i64 boundary. This gap closes when BigInt support lands (see
> roadmap); until then it is the one place the compiler silently assumes
> something it hasn't proved.

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

### Bool domain and range

`Bool` is a first-class set like any other — it can appear as a domain or range, and Bool values compose naturally with boolean operators.

```haskell
is_positive : Int -> Bool
is_positive(x) = x > 0

negate : Bool -> Bool
negate(b) = not b

to_nat : Bool -> Nat
to_nat(b) = if b then 1 else 0
```

```sh
$ cantor bool_demo.cantor
  proved          is_positive : Int -> Bool
  proved          negate : Bool -> Bool
  proved          to_nat : Bool -> Nat

  3 proved, 0 counterexample(s), 0 unknown
```

Bool values are distinct from integers so accidental conversion to 0 or 1 isn't possible.

### Constants

Constants are compile-time values, checked against their declared range constraint set.
They are automatically inlined everywhere they are used.

```haskell
scale : Nat = 1000
pi_scaled : Nat = 3 * scale + 141

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
clamp : Int * Nat * NatPos -> Nat | Fail
clamp(x, lo, hi) {
    assert lo < hi        -- not provable from the domain (lo=5, hi=3 fits it),
                          -- so this becomes a runtime check — hence `| Fail`
    if x < lo then lo else if x > hi then hi else x
}

to_nat : Int -> Nat
to_nat(x) {
    assume x >= 0         -- escape hatch: "honest guv! the solver can't see it,
                          -- but I just KNOW the caller only passes x >= 0"
    x                     -- proved (from the assume); unsound if the caller lies
}
```

`require` is a compile-time proof obligation — a hard error if it can't be proved.
`assert` graduates: if provable, it's elided; if always false, it's a compile error; if unknown, it becomes a runtime check — which is why a function containing an unproved `assert` must declare `| Fail` in its range.
`assume` is an escape hatch: no check, no proof — the compiler simply believes you, and every proof downstream is worthless if you lied.

The better fix for `clamp` is no runtime check at all: put the relationship in the
domain — `{(x, lo, hi) ∈ Int × Nat × NatPos | lo < hi}` — so every *caller* must
prove it, which is the whole point of the language. Compound relational domains
are part of the design (see `docs/design-decisions.md` §10) but not implemented yet.

### Mutables, mutation invariants and loops

Within blocks `mut name: Set = expr` is used to declare a mutable local along with it's **range invariant** — the set the variable must remain in across every mutation.

The syntax for _reassignment_ is `:=` to distinguish it from introducing a new name. Each reassignment is required to fit within the declared range.

This is most commonly used within `while` loops:

```haskell
sum_to : Nat -> Nat
sum_to(n) {
    mut acc: Nat = 0   -- 0 ∈ Nat ✓  (init); Nat is the invariant for acc
    mut i: Nat = 1     -- 1 ∈ Nat ✓  (init)
    while i <= n {
        acc := acc + i  -- acc + i ∈ Nat checked
        i   := i + 1    -- i + 1 ∈ Nat checked
    }
    acc                -- acc ∈ Nat from invariant + ¬(i <= n) → ℵ proved
}
```

```sh
$ cantor sum_to.cantor
  ℵ proved   sum_to : Nat -> Nat
```

The declared constraint is used in three places: the initial value is checked against it, each reassignment asserts the new value satisfies it, and after the loop the post-loop SSA variable inherits it as a known fact.

**The compiler verifies the inductive step.**
Before trusting the invariant for post-loop reasoning, the solver checks that one body iteration actually maintains it: given `acc ∈ Nat` and the loop condition, does `acc := acc + i` leave `acc` still in `Nat`?
The same check discharges every built-in obligation the body produces — division domains, vector bounds, call-site domains, unproved `assert`s — under the induction hypothesis, so `i := i + 10 / i` is a counterexample (`i` starts at 0), not a proved crash.
If the step cannot be proved — for example, `mut acc: Int16 = 0` with `acc := acc + 1` in an unbounded loop — the compiler reports a counterexample immediately rather than a false `proved`.
Loop variables declared as `mut name: Int` carry no effective constraint (Int = all integers) and behave conservatively: if the range obligation depends on such a variable, the result is `unknown` rather than a potentially spurious counterexample.

### For-in loops

`for x in S` iterates over a set, binding `x` to each element in turn.
The same loop invariant mechanism applies: `mut acc: Set` declares the invariant, and the compiler verifies it is maintained across every element.

```haskell
sum_set : -> Nat
sum_set() {
    mut acc: Nat = 0
    for x in {1, 2, 3} {
        acc := acc + x
    }
    acc      -- acc ∈ Nat proved inductively over all elements
}
```

Naming the loop variable with an uppercase letter (`for X in {1, 2, 3}`) promises that the value is known at compile time and forces the compiler to verify the iterable is statically materializable — a lightweight way to opt into guaranteed compile-time unrolling.

### Runtime sets

`Set(Int)` and `Set(Bool)` are first-class runtime values.
`mut s : Set(Int) = {e1, e2, …}` allocates a heap-backed sorted-unique set; duplicates are collapsed silently.
`for x in s` iterates the elements in sorted order, `x in s` / `x not in s` test membership, and `size(s)` returns the cardinality.

```haskell
main : -> Int
main() {
    mut primes : Set(Int) = {2, 3, 5, 7}

    mut acc : Int = 0
    for p in primes {
        acc := acc + p        -- acc = 17
    }

    mut checks : Int = 0
    checks := if 3 in primes     then checks + 1 else checks   -- 3 is prime ✓
    checks := if 4 not in primes then checks + 1 else checks   -- 4 is not   ✓

    acc + checks + size(primes)   -- 17 + 2 + 4 = 23
}
```

```sh
$ cantor run primes.cantor
  proved          main : -> Int

  1 proved, 0 counterexample(s), 0 unknown

main() = 23
```

The solver models runtime sets as opaque values and treats membership and `size` as unconstrained integers, which is sufficient to prove `Int`-range signatures statically.

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
        acc := acc + y
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
        acc := acc + y
    }
    acc
}
```

### Distinct sets and unit safety

`distinct` creates a new solver-opaque set that is disjoint from its basis type.
The compiler auto-provides a constructor and `from` as a destructor.

```haskell
Litre  = distinct Nat
Kelvin = distinct NatPos

-- litre : Nat -> Litre  (auto-provided)
-- from  : Litre -> Nat  (built-in destructor)

scale : Litre -> Litre
scale(v) = litre(from(v) * 2)   -- double the underlying Nat, re-wrap as Litre

freeze : -> Kelvin
freeze() = kelvin(273)           -- 273 wrapped with the constructor: proved ✓
```

```sh
$ cantor distinct_demo.cantor
  proved   scale  : Litre -> Litre
  proved   freeze : -> Kelvin
```

Accidentally passing a plain `Nat` where a `Litre` is expected, or forgetting the constructor, produces a counterexample rather than a silent pass.

### Product Sets

Functions can take and return elements of product sets (aka tuples) using `*` in signatures and `(e1, e2)` syntax in bodies. Positional projection uses `.0`, `.1`, etc.

**Nesting and associativity.** `*` is a flat n-ary product at each
parenthesization level, mirroring tuple-literal syntax: `Int * Int * Int` is the
set of flat triples like `(1, 2, 3)`, while `(Int * Int) * Int` is the set of
*pairs* whose first element is a pair, like `((1, 2), 3)`. So `A * B * C`,
`(A * B) * C`, and `A * (B * C)` are three different sets — parentheses nest,
exactly as they do in value literals. A named set substitutes as-if-parenthesized:
given `Pair = Int * Int`, the set `Pair * Int` means `(Int * Int) * Int`
(pairs-of-pair-and-int), *not* flat triples — otherwise expanding a transparent
alias would change the set it denotes.
(Implementation note: the parser currently flattens `*`-chains through
parentheses, so parenthesized nesting is not yet honoured — TODO.)

```haskell
swap : Int * Int -> Int * Int
swap(t) = (t.1, t.0)

-- The compiler proves fst(t) ∈ Nat given t ∈ Nat * Nat
fst : Nat * Nat -> Nat
fst(t) = t.0

main : -> Int * Int
main() = swap((3, 9))
```

```sh
$ cantor run tuple_demo.cantor
  proved          swap : Int * Int -> Int * Int
  proved          fst : Nat * Nat -> Nat
  proved          main : -> Int * Int

  3 proved, 0 counterexample(s), 0 unknown

main() = (9, 3)
```

The compiler also catches when a range claim fails for tuple operations:

```haskell
overflow_pair : Int16 * Int16 -> Int16
overflow_pair(t) = t.0 + t.1   -- sum can exceed Int16 range
```

```sh
$ cantor overflow.cantor
  counterexample  overflow_pair : Int16 * Int16 -> Int16
    t = 0  ->  output = -32769  (not in Int16)
```

**Destructuring**

`f : Int * Int -> Int` with `f(x, y)` means two separate scalar parameters; `f : Int * Int -> Int * Int` with `f(t)` means a single tuple parameter. The number of declared parameters determines which reading applies — no extra syntax needed.

Destructuring assignment works as you would expect for tuples.
The only requirement is that the compiler can statically prove that your tuple has at least as many elements as binders that you request — trivially true, since a tuple's arity is fixed at compile time.

```haskell
x, y = (a, b) -- alias constants x=a, y=b by constructing and destructuring a tuple

f : Int * Int * Int -> Int
f(p) {
    x, y, z = p        -- pattern match on a tuple parameter directly
    x + y + z
}

h, t = (1, 2, 3, 4, 5) -- h == 1 and t == (2, 3, 4, 5)
                       -- with fewer binders than elements the tail is placed into the last element
```

> **Known limitations:**
> - Destructuring a *vector* (`X*`) is not yet implemented, whether as a
>   `let`/`:=` statement (`h, t = v` for `v : Nat*`) or as function parameters
>   (`foo(x, y)` on a single vector-typed domain), so that `h`/`x` binds the
>   head element(s) and `t`/`y` binds the remaining elements as a vector tail.
>   This would need a solver-proved length obligation (the vector must have at
>   least as many elements as binders requested) and new codegen support for
>   slicing an Arrow vector — currently rejected at compile time with a clear
>   error rather than silently doing the wrong thing.
> - Destructuring a *locally `let`-bound tuple variable* (`v : Int * Int = (1, 2); x, y = v`)
>   currently crashes the solver — tuple destructuring only works directly on
>   a tuple literal or a tuple-typed function parameter (both shown above).
>   Tracked as a compiler bug, not a design limitation.

### Vectors and bounds safety

`X*` is a variable-length sequence of values from the set `X`.
The built-in `len(xs)` returns the length; `xs[i]` indexes by position; `++` concatenates two vectors.

Like [divide by zero](#division-safety), **out-of-bounds indexing is a class of safety violation that Cantor catches by proof.**

When the length is statically known — because the vector was built from a literal — the compiler proves the index is safe and no check is needed:

```haskell
first_elem : -> Nat
first_elem() = [10, 20, 30][0]    -- proved: index 0 < 3 ✓

third_field : -> Nat
third_field() = [(1, 10), (2, 20), (3, 30)][2].1    -- proved: index 2 < 3 ✓
```

When the vector or index is only known at runtime, the compiler cannot prove safety and gives a counterexample — just as it does for division:

```haskell
head : Nat* -> Nat
head(xs) = xs[0]
```

```
$ cantor head.cantor
  counterexample  head : Nat* -> Nat
    xs = []  ->  (vector index 0 may be out of bounds)
```

The solver found that an empty vector makes index 0 invalid.
If you can't justify why the index is in range, you have no business indexing.

To pass the check, restrict the domain so the compiler has enough information, or add an `assert` to insert a runtime guard:

```haskell
-- Explicit runtime guard: turns the obligation into a checked failure
safe_head : Nat* -> Nat | Fail
safe_head(xs) {
    assert len(xs) > 0 else fail
    xs[0]
}
```

With a runtime-variable index the same story applies — `assert i < len(xs) else fail` is the escape hatch when the compiler can't see a static proof:

```haskell
nth : Nat* * Nat -> Nat | Fail
nth(xs, i) {
    assert i < len(xs) else fail
    xs[i]
}
```

Vectors of tuples (`(Nat * Nat)*`) and nested vectors (`Nat**`) work the same way — the bounds obligation is attached to any indexing expression, and a literal-length vector with a literal index is always proved statically.

Vectors are resticted to have a length representable by a single machine word. If you are writing for a system with segmented memory then you'll need to split your incredibly long vectors into segments!
Hopefully that will help you feel right at home.

#### Scalars and tuples coerce to sequences

Every scalar `n` may be used where a length-1 sequence is expected, and every tuple
`(a, b, c)` where a length-3 sequence is expected. This is a **membership-level
coercion, not an identity**: `5 ∈ Nat*` holds (as the length-1 sequence `[5]`),
but `5 == [5]` is a domain error, and `len` is only defined on genuine sequence
values. The coercion exists because `(5) == 5` — parentheses are overloaded for
grouping and tupling, so there is no distinct "1-tuple" sitting between a scalar
and a singleton sequence.
The compiler automatically boxes a scalar or tuple into an Arrow vector when crossing a `X*` function boundary:

```haskell
foo : -> Nat*
foo() = 5            -- proved: 5 coerces to the length-1 sequence [5]

get : (Nat* - {[]}) -> Nat
get(xs) = xs[0]

val : -> Nat
val() = get(5)       -- proved: 5 is boxed to [5] before the call
```

> **Note:** boxing allocates a singleton Arrow array on every call.
> The scalar-stays-i64 optimisation (when the callee is statically known to consume exactly one element) is on the roadmap but not yet implemented.

#### Length-narrowing with set difference

Because scalars coerce to length-1 sequences and tuples to length-N sequences, set difference narrows the _length_ of a domain:

| Domain expression | Meaning |
|-------------------|---------|
| `Nat*`              | all non-negative integer sequences (any length) |
| `Nat* - {[]}`       | non-empty Nat sequences (length ≥ 1) |
| `Nat* - Nat`        | Nat sequences of length ≠ 1 |
| `Nat* - Nat - {[]}` | Nat sequences of length ≥ 2 |

The special literal `{[]}` is the set containing the empty sequence
(`{}` itself is always the ordinary empty set — the two are not interchangeable).
Combined, these let the compiler prove that multi-element access is safe:

```haskell
h : (Nat* - Nat - {[]}) -> Nat   -- length ≥ 2
h(xs) = xs[0] + xs[1]             -- proved: both indices in range
```

### Fixed-length arrays

`X * N` in a signature is sugar for the N-fold Cartesian product `X * X * … * X`, making it easy to write functions over fixed-size collections without spelling out every component.

```haskell
sum3 : Nat * 3 -> Nat
sum3(x, y, z) = x + y + z

fst3 : Int * 3 -> Int
fst3(t) = t[0]
```

```sh
$ cantor arrays.cantor
  proved          sum3 : Nat * 3 -> Nat
  proved          fst3 : Int * 3 -> Int
```

The compiler proves that, for example, `sum3` maps any three natural numbers to a natural number, and that projecting element 0 of a `Int * 3` value is still an `Int`.

**Array literals** `[1, 2, 3]` construct a fixed-length array and can appear anywhere a tuple literal `(1, 2, 3)` is valid. The two are identical at runtime — `[1, 2, 3]` is syntactic sugar for `(1, 2, 3)`.

In most other languages square brackets communicate that the type of every value must be homogenous.
But in Cantor `[1, true, 3]` can be seen as a homogenous tuple in the set `(Int | Bool) * 3` - which is homogenous, just a bit weird.

So in Cantor most of the time square brackets don't communicate homogeneity, they just communicate "I like square brackets".

The only exception to this case is where the compiler is automatically inferring a suitable range for a value: `(x, y, z)` can have any range of the form `X * Y * Z` but `[x, y,z]` will be inferred to have a range of the form `X * X * X`.

**Bracket indexing** `t[N]` is an alias for `t.N`, keeping a consistent `t[i]` indexing syntax that extends naturally to the runtime-variable indices used with Kleene-star vectors.

```haskell
nat_triple : -> Nat * 3
nat_triple() = [1, 2, 3]

mid : Int * 3 -> Int
mid(t) = t[1]
```

The compiler proves `[1, 2, 3]` satisfies the `Nat * 3` range, and that `t[1]` on an `Int * 3` input is an `Int`.

## Features (working today)

- **Set-theoretic domains and ranges** — `Int`, `Nat`, `NatPos`, `NonZeroInt`, `Int8`–`Int64`, `Bool`, set literals `{0, 1, 2}`, set difference `A - B`, union `A | B`, intersection `A & B`, error-union `A !! B` (why? because when you get an error the code goes bang! bang! ... I'll let myself out ...)
- **Bool as a first-class value kind** — `Bool` is disjoint from all integer sets; comparisons (`>`, `==`, …) produce `Bool`; `and`, `or`, `not` operate on `Bool`; no implicit coercion between `Bool` and integers
- **Set comprehensions** — `{ expr for x in S if pred(x) }` in domain/range/`in`/`for` positions; finite literal sources unrolled statically; infinite named sources encoded as SMT predicates
- **Product Set values (aka tuples)** — `f : Int * Int -> Int * Int`; tuple literals `(e1, e2)`; positional projection `t.0`, `t.1`; tuples as parameters and return values; the compiler proves tuple domain and range claims end-to-end; `cantor run` prints tuple results as `(a, b)`. Disambiguation: `f(x, y)` with two params = two scalars; `f(t)` with one param = single tuple.
- **Fixed-length arrays** — `X * N` in a signature desugars to the N-fold Cartesian product `X * X * … * X`; array literals `[e1, e2, e3]` are syntactic sugar for tuple literals `(e1, e2, e3)`; bracket indexing `t[N]` is an alias for `t.N`
- **Variable-length vectors** — `X*` (Kleene star) for runtime-variable-length sequences; `len(xs)` for cardinality; `xs[i]` with a runtime index; `xs ++ ys` concatenation; vectors of tuples `(A * B)*` (columnar Arrow backing) and nested vectors `X**` (ListArray backing). Scalars and tuples coerce to sequences at membership level (a scalar `n` may stand in for the length-1 sequence `[n]`, an N-tuple for the length-N sequence — a coercion, not an identity), so `foo() = 5 : Nat*` is valid and the compiler boxes the scalar automatically at function boundaries. Length-narrowing set difference: `Nat* - Nat` restricts to length ≠ 1, `Nat* - Nat - {[]}` to length ≥ 2. Bounds safety: literal-length vectors with literal indices are proved statically; runtime-length or runtime-index access generates a bounds obligation — a counterexample is reported unless the compiler can prove the index is always valid, otherwise an `assert` inserts a runtime guard
- **SMT-backed proof** — every function signature is proved, disproved (with a counterexample), or flagged unknown using cvc5
- **Interprocedural checking** — callee contracts are used modularly; recursion works via the function's own signature as an induction hypothesis; every call site carries a proof obligation that the arguments lie in the callee's declared domain (for overloads: in at least one of them), so an out-of-domain call — including a recursive one — is a counterexample, never a silent assumption; `?` narrows the result to the success arm per-signature, guarded by that signature's domain
- **Unified named definitions** — constants (`pi : Nat = 314`) and compile-time set definitions (`Colour = {1, 2, 3}`) share the same one-line syntax and the same AST node; both are auto-inlined at compile time; constants are checked against their range annotation
- **Block bodies with `while` and `for x in S` loops** — imperative-style bodies with `while cond { stmts }` and `for x in {e1, e2, …} { stmts }`, `mut name: Set = expr` locals (set annotation is the declared loop invariant), sequenced statements, and `if-then-else`
- **Runtime sets** — `Set(Int)` and `Set(Bool)` as first-class heap-allocated values; `mut s : Set(Int) = {…}` creates a sorted-unique set; `for x in s` iterates; `x in s` / `x not in s` test membership; `size(s)` returns cardinality; duplicates are collapsed silently
- **`require` / `assert` / `assume`** — static and graduated runtime proof obligations
- **`Fail` and `?`** — monadic error propagation; fallible functions declare `| Fail` in their range; `?` short-circuits on failure
- **`fail` and `fail expr`** — `fail` produces the bare failure sentinel; `fail 400` constructs a tagged failure with integer payload (used with `!!`)
- **Named error sets and error-union** — `HTTPError = {400, 503}` defines an error set; two ways to use it in a range:
  - `fetch : NatPos -> Nat | HTTPError` — plain set union; valid as a range when the **success set and error codes are disjoint** (e.g. `NatPos` doesn't contain 400 or 503); the value carries no runtime tag, so distinguishing success from error is the caller's job via set membership. `?` is **not** available on plain unions — propagation requires the fallible `{i1, i64}` wire of `| Fail` / `!!`
  - `fetch : Int -> Int !! HTTPError` — error-union operator; use when success values and error codes may overlap (any `Int` could legitimately be 400); `fail 400` builds the `{i1=1, i64=400}` failure struct, so `?` always distinguishes `fail 400` from success `400` by the flag bit, never by the value; **caller must declare `| Fail` or `!!` in its own range**
- **`return expr`** — early return from a block body; the solver models `return` in flat blocks exactly (at any statement position); a `return` inside a `while`/`for` body is still reported `unknown` — never a false proof
- **`assert … else fail/return`** — `assert pred else fail 400` returns the offset-encoded failure when the predicate is false; `assert pred else return expr` returns `expr` directly as an early success exit
- **Named set naming convention** — uppercase names are compile-time set names (`Nat`, `HTTPError`); lowercase names are values (`pi`, `abs`, `collected_primes`); enforced by the compiler
- **`alias` and `distinct` set modifiers** — `Colour = {1, 2, 3}` and `Animal = alias Cat | Dog` declare transparent aliases (the solver expands membership inline); `Litre = distinct Nat` declares a new solver-opaque set disjoint from `Nat` with full SMT-backed value proofs (see below)
- **`distinct` value proofs** — `Litre = distinct Nat` automatically provides the constructor `litre : Nat -> Litre` and the built-in destructor `from(x)` which returns the basis-type value. The solver gives each distinct set its own uninterpreted CVC5 sort plus uninterpreted constructor/destructor functions (`mk_Litre : Int -> Litre`, `from_Litre : Litre -> Int`); basis-set constraints are emitted on demand at each `litre(n)` / `from(x)` site (no global axioms; logic `ALL`); identity functions (`volume : Litre -> Litre`) are proved directly. Plain integer literals not wrapped in a constructor are correctly rejected with a counterexample. Both `litre` and `from` are identity operations at runtime. `from` and `size` are reserved keywords.
- **JIT execution** — `cantor run <file>` checks proofs then JIT-compiles and runs `main` via LLVM
- **LLVM IR dump** — `cantor llvm-ir <file>` skips the SMT solver and prints the compiled LLVM IR to stdout, for debugging codegen without JIT-running anything

## On the roadmap

- **Vector iteration** — `for x in xs` over a `X*` vector; the remaining iteration pattern to complement the existing `len`, `xs[i]`, and `++` operations. Includes support for a `Size` set that aliases the machine word size, e.g. `Nat64`.

- **Function overloading and pattern matching** — functions can be overloaded on distinct sets, `match x { Shape.Circle(r) => …, Shape.Rect(w, h) => … }` or some similar syntax for pattern matching

- **Namespaces and named structured data** — Named product sets (`Point = distinct (x: Metre, y: Metre)`; field access via `p.x`), and named union sets (`Shape = distinct (Circle: Nat | Rect: Nat * Nat)`; construction via `Shape.Circle(r)`). Products have projections, coproducts have injections — the syntax makes the duality explicit.

- **Quotient sets and wrapping arithmetic** - Quotient sets to be defined by a canonicalizer, which would let us write `WrappingNat32 = distinct Nat / (x -> x mod 2^32) deriving Arithmetic + ...`. Built in quotient sets for native machine arithmetic.

- **Lambdas, closures, and higher-order functions** — anonymous functions, captured variables, and functions as first-class values. Unlocks `map`, `filter`, `fold`, and combinators without needing the full generics machinery.

- **`raise` and `emits`** — unrecoverable errors (raised at the event loop boundary; Class 2 errors roll back state atomically) and write-only side effects (logging, metrics); both are fully inferred from the call graph, no annotation required.

- **State** — mutable program state that survives between calls, proved to satisfy its invariants at every event boundary. Completes the `(Event, State) → (Output, State)` model.

- **Module system** — imports, library compilation, separate checking; one file = one module, `::` path separator.

- **More built-in values and collections** — floats, rationals, characters, bytes, ordered sets, maps.

- **Generics** — a single new keyword `given` introduces a compile-time variable into scope; `require` states constraints on it. The generic body is checked once at *definition* time against the `require` facts alone (the Rust-trait model, not the C++-template model), so instantiation can never fail post-hoc — it only proves the concrete set satisfies the stated constraints. Reduces to an overload generator with no other new machinery: `given A; require A <= Countable; population : Habitat(A) -> Nat`.

- **Dependent ranges** — let a range reference named domain binders, e.g. `div : {(x, y) ∈ Int × NonZeroInt} -> {q ∈ Int | q * y <= x}`, so callers learn more than bare set membership from a signature. A deliberately reserved design opening: the comprehension machinery (captures, membership encoding) already covers the semantics.

- **Smarter diagnostics** — when the solver can't prove a claim, it extracts an unsat core and suggests the minimal constraints that would close the proof gap. Also: automatic inference of the range annotation on `mut` locals so you don't have to write it by hand.

- **Advanced compiler capabilities** — two related long-game items: switching to cvc5's native `Sets` theory for proofs that must reason about every element of a filtered set; and feeding proved facts (purity, bounds, non-aliasing) to LLVM as `assume`/`range` metadata so proofs become optimisations for free.

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
- Apache Arrow (`arrow-array` crate, fetched automatically by Cargo)

```
cargo build
cargo test

cargo run -- <file.cantor>          # check proofs
cargo run -- run <file.cantor>      # check then JIT-run main()
```

## Development process

Luckily for me it's been 152 years since Cantor published ["_Ueber eine Eigenschaft des Inbegriffes aller reellen algebraischen Zahlen_"]([https://en.wikipedia.org/wiki/Cantor%27s_first_set_theory_article](https://en.wikipedia.org/wiki/Georg_Cantor#Set_theory)) and not only do we have unbelievely powerful silicon computers, that silicon can _think_ and _write code_ and sometimes even tells me cat jokes.

This means that essentially 100% of the code in Cantor is LLM-generated, along with much of the documentation. My role has been to read and understand the code in order to guide the LLM on it's intrepid journey across compiler-space.

So when I say "learn Rust" what I really mean is "learn _to read_ Rust", I almost certainly can't actually write it succesfully if I were given a blank slate and no docs.

If for some reason you happen to be reading this _and_ you happen to notice the LLM-generated code is somehow off (buggy, non-idiomatic, just looks plain weird) then please let me know so I can either fix it or learn something new! But also, why _are_ you still reading this? Don't you have something better to do? Go spend time with your cat!
