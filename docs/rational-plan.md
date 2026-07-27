# `Rational` and the numeric tower: plan

**Status: design drafted 2026-07-27, not yet implemented.** Three forks were
resolved with Doug before writing this:

1. **`Int ⊆ Rational`** — a genuine numeric tower, not a disjoint sort.
   `2 in Rational` is true; an `Int`-Kinded value implicitly widens where a
   `Rational` is expected; narrowing back to `Int` is a *proof obligation*,
   never implicit. This is deliberately the opposite stance from
   `Signed32`/`Unsigned32`/`Char` (all fully disjoint) — and it is not a
   softening of the `Bool`≠`Int` rule (see `feedback_bool_int_disjoint`),
   because ℤ ⊂ ℚ is a real subset relation, whereas `true`/`1` merely share a
   bit pattern.
2. **Boxed exact representation** — a `Rational` value is an arena-allocated
   pointer word to a `num_rational::BigRational`, mirroring
   `cantor-runtime/src/bigint.rs`. Exact, never overflows, one i64 leaf.
3. **No `tdiv`/`trem`** — design-decisions.md currently promises a truncating
   division pair once `Rational` lands. That promise is **retracted**:
   Euclidean `quot`/`rem` already exist and cover integer division; a second,
   differently-rounding pair is surface area for no gain.

Confidence is called out inline. The solver plan is high-confidence (the cvc5
kinds were verified present, and the range-check mechanism was traced end to
end); the widening-site inventory is medium — see "Known soft spot" at the end.

---

## Why now

`3 / 2` currently produces an integer. Two separate notes already anticipate
this change: backlog.md:105, and the `<!-- TODO -->` block at
design-decisions.md:2043-2053, which labels today's `/` a
"rapid-prototyping-era placeholder".

There is also a **live correctness bug** this closes. The solver encodes `/`
as cvc5 `IntsDivision` (SMT-LIB `div` — Euclidean, remainder always
non-negative) at `src/solver/encode.rs:651`, while codegen emits LLVM `sdiv`
(truncating toward zero) at `src/codegen/arith.rs:124`. These disagree for
negative operands: the solver believes `(-7) / 2 == -4`, the runtime computes
`-3`. Any proof about `/` over a domain admitting negatives is currently
unsound. Retiring integer `/` retires the disagreement.

## The payoff

Range checking is *already* set-membership based, not Kind-comparison based:
`sig_check::finish` (`src/solver/sig_check.rs:229-275`) builds the range
obligation by calling `membership_constraint(body_term, range_expr)`. So once
`/` yields a Real-sorted term, this falls out with **no new machinery**:

```
f : Int * NonZeroInt -> Int
f(a, b) = a / b        -- counterexample: a=3, b=2 → 3/2 ∉ Int

g : Int -> Int
g(x) = (2 * x) / 2     -- proved; elides to the Int representation

h : Rational -> Rational
h(q) = q + 1           -- 1 widened to 1/1
```

`a / b ∈ Int` becomes a divisibility theorem the solver discharges. That is
the language's whole pitch, obtained by deleting a special case rather than
adding one.

---

## Where this sits

`Int64`/`BigInt` (int-soundness-plan.md) is a **codegen representation split**
underneath the single mathematical set `Int` — one Kind pair, `Int64 ⊆ Int`,
reconciled by `IfMerge::CoerceInt64ToInt` (`src/kind.rs:573`) and
`coerce_int_return` (`src/codegen/coerce.rs:236`). That is the only existing
non-disjoint Kind pair, and it is the direct precedent for this work:
`Int ⊆ Rational` needs the same shape of coercion at the same boundaries, one
level up.

`Signed32`/`Unsigned32`/`Char` are *not* the precedent — those are disjoint
sorts with no coercion anywhere.

---

## Stage 1 — Kind, builtin, elaboration

- `Kind::Rational` in `src/kind.rs`. Excluded from `is_scalar_word_kind`
  (pointer identity ≠ value equality — the same blocker that already defers
  `Set(Int)` with BigInt elements). Included in
  `is_distinct_basis_representable` (Real is a perfectly good basis sort).
- `"Rational"` in `semantics::builtins::lookup`. `IntBound` is meaningless
  here, as it already is for `Bool`/`Fail`/`Char` — `IntBound::Any` filler,
  with the same comment those entries carry.
- `elaborate::binop`'s `BinOp::Div` / `Position::Value` arm
  (`src/semantics/elaborate/binop.rs:106-112`) reports `Kind::Rational`
  instead of `Kind::Int`. `Position::Set` (quotient-set formation) is
  untouched — the two readings were separated from the start.
- `arith_value_kind` (`src/semantics/elaborate/binop.rs:310`): if either
  operand is `Rational`, the result is `Rational`. This is the widening rule
  for `+ - *`.
- `is_ordered_pair` (`:323`): admit `Rational`, and admit mixed
  `Int`/`Rational` comparison (widening the Int side). Note the existing
  `l == r` guard deliberately rejects `Signed32 < Unsigned32`; the mixed case
  must be added explicitly rather than by loosening that guard, or the
  disjoint sorts leak through.
- `set_kind`'s `BinOp::Div` arm (`src/kind.rs:357`) is the *set*-position
  quotient reading — unchanged.

Everything downstream fails loudly (`Unsupported`) until stages 2-3 land.

**Note:** `Rational` cannot be spelled in-language as `Int / Int`, because `/`
in set position already means quotient formation. It must be a builtin name.
No ambiguity arises — the two positions are elaborated separately.

## Stage 2 — Solver

- `scalar_kind_sort` / `set_sort` (`src/solver/sort.rs:31`): `Kind::Rational`
  → `tm.real_sort()`. `arm_ctor_name` → `"ck_Rational"`. The module's own
  "how to add a new sort" checklist (`src/solver/sort.rs:122-130`) lists the
  five sites; this feature is exactly that checklist plus coercion.
- `encode_binop` (`src/solver/encode.rs:651`): `BinOp::Div` → cvc5
  `Kind::Division` (26, real division) rather than `IntsDivision` (28).
  `Quot`/`Rem` keep `IntsDivision`/`IntsModulus` and keep integer-sorted
  operands.
- **Sort unification at mixed sites.** cvc5 is strictly sorted; an
  Int-sorted and a Real-sorted operand cannot meet directly. Wrap the Int
  side in `Kind::ToReal` (57). Confidence: high that this is required, medium
  on the exact inventory of sites — `encode_binop` and the comparison
  encoder are certain, the union-DT coercion path (`coerce_to_union_dt`)
  needs checking.
- **`membership.rs:343-372` is the critical site.** Today a Real-sorted term
  hits `t.sort().is_integer()` → false (for `IntBound::Any`) or
  `to_integer_term(t)` → `None` (for every bounded variant), and returns a
  hard `false`. Both branches need a Real case:
  - `Int`: `IsInteger(t)` (kind 55).
  - `Nat`/`NatPos`/`NonZeroInt`/`IntN`/`BigInt`: `IsInteger(t) ∧ bound(ToInteger(t))`
    (kind 56).
  - `Rational` itself: a Real-sorted term is trivially a member; anything
    else is not — same shape as the `Signed32` arm just above it.

  This one function is what makes the divisibility obligation in "The payoff"
  work. High confidence: the cvc5 kinds were verified present in the 0.4
  bindings (`Division = 26`, `IsInteger = 55`, `ToInteger = 56`,
  `ToReal = 57`, plus `real_sort` and `mk_real_from_rational`).
- **`binary_builtin_domain` must become Kind-aware**
  (`src/solver/obligations.rs:164`). It currently returns a hardcoded
  `NonZeroInt` for `/`'s divisor regardless of operand Kind. With a Rational
  divisor that obligation is not merely too strong, it's *wrong* — a
  Rational is not a member of `NonZeroInt`, so a perfectly valid
  `q / (1/2)` would be rejected. Needs either a `NonZeroRational` builtin or
  a Kind-parameterised obligation. **Open question — see below.**
- **Overflow obligations must skip Rational nodes.** Exact arithmetic cannot
  overflow, so emitting an `Int64`-fit claim for a Rational-Kinded
  `Add`/`Sub`/`Mul`/`Div` is both meaningless and noisy.
- **`int64_split` must not promote or split Rational expressions**
  (`src/solver/int64_split.rs`) — that machinery reasons about raw i64
  representability, which has no Rational analogue.
- Decidability: LRA/LIRA are decidable, so this should not make proofs
  harder. Nonlinear rational arithmetic is as hard as nonlinear integer
  arithmetic already is — no regression, no improvement.

**Regression risk is low by construction:** programs with no `/` and no
`Rational` annotation never produce a Real-sorted term, so their encoding is
byte-for-byte what it is today.

## Stage 3 — Codegen and runtime

- New `cantor-runtime/src/rational.rs`, modelled directly on `bigint.rs`:
  arena-allocated `CantorRational(BigRational)`, pointer word, entry points
  `cantor_rational_{add,sub,mul,div,neg,cmp,eq,from_int,is_integer,to_int,show}`.
  `num-rational` on top of the existing `num-bigint` dependency. Always
  normalized (gcd-reduced, positive denominator) — `num-rational` does this.
- `kind_to_llvm_type` (`src/codegen/mod.rs:213`): `Kind::Rational` → i64
  (pointer-as-i64, same as `Set`/`Vector`). `leaf_count`
  (`src/codegen/wire.rs:18`) → 1, so no structural wire change.
- `compile_arith` (`src/codegen/arith.rs:35`): a Rational-Kinded operand
  routes to the `cantor_rational_*` calls, widening any Int operand via
  `cantor_rational_from_int` first. Structurally this mirrors the existing
  `tagging_active()` branch at `:82` that routes to `cantor_bigint_*`.
- **Widening sites** (the Int→Rational boundary inventory):
  - call arguments — `coerce_call_arg` → `coerce_to_kind`
    (`src/codegen/coerce.rs:263,285`). Note `coerce_to_kind`'s
    `_ => Ok((val, val_kind))` fallthrough at `:299` currently passes a
    mismatched scalar Kind straight through; an Int→Rational arg would
    silently produce a wrong-typed LLVM value there. **This is the arm to
    extend, and the most likely place to get a latent bug.**
  - function return — `coerce_int_return` (`:236`), which is already
    Int/Int64-specific and is the natural home for the Int/Rational case
    (called from `mod.rs:654,726` and `blocks.rs:483`).
  - `if`-merge — a new `IfMerge::CoerceIntToRational` variant
    (`src/kind.rs:537`) plus its arm in `merge_if_branches` (`:598`) and in
    `codegen/expr.rs:203`.
  - declared `let`/`mut` bindings annotated `: Rational`.
  - comparisons and `==`. **`==` must call `cantor_rational_eq`, not compare
    pointers** — two allocations can hold the same value.
- `show` (`src/codegen/show.rs`): `show(3/2)` → `"3/2"`, `show(4/2)` → `"2"`
  (normalized, denominator 1 prints bare).
- **Deferred with a clean `Unsupported`, not a silent fallback:**
  `Set(Rational)` and `Vector(Rational)` (value-equality blocker above), and
  event-loop `State` containing a Rational
  (`wire.rs::state_leaf_shape` / `vector_elem_shape` — arena deep-copy).

## Stage 4 — Migration and diagnostics

~36 Cantor-level `/` sites across the test suite move to `quot` (heaviest:
`tests/solver/membership.rs` 10, `tests/solver/encode.rs` 8,
`tests/solver/loops.rs` 7). Some should *stay* as `/` and become
divisibility-proof tests instead — that is the new headline behaviour and
needs positive coverage, not just migration.

The diagnostic matters more than the migration. An `Int`-ranged function with
a `/` body must not report a bare "not in Int" membership failure; it needs to
name the cause and the fix — "`/` produces a `Rational`; use `quot` for
integer division". Per CLAUDE.md this is a `Diagnostic`, not an `Ice`.

## Stage 5 — Documentation

Single commit, per CLAUDE.md. design-decisions.md: rewrite the "Arithmetic
widening" bullet at :2039 and **delete** the `<!-- TODO -->` block at
:2043-2053 (both the truncating-`/` note and the `tdiv`/`trem` promise);
update the deferred-features entry at :1889; note the numeric tower in §13.
wrapping-and-quotient-sets-plan.md:416-423 has forward-pointers to
`Rational`/`tdiv`/`trem` that need reconciling. backlog.md:105 closes.

Plus CLI end-to-end tests, per CLAUDE.md.

---

## Open questions

1. **`/`'s divisor obligation over rationals.** Add a `NonZeroRational`
   builtin, or make `binary_builtin_domain` Kind-parameterised and express
   "nonzero" per Kind? The latter is less user-visible surface and avoids a
   name nobody will ever write by hand; the former reuses the existing
   named-set obligation path unchanged. Leaning Kind-parameterised, but this
   needs a look at how the obligation's failure message reads in each case.
2. **`Nat`/`NatPos` analogues over ℚ** — is there a `PosRational`? Not needed
   for `/` to work. Recommend shipping none in v0 and adding on demand.
3. **Decimal literals.** `0.5` does not lex today and should stay that way
   for now — it reads as a float, which is a different (and much larger)
   feature. `1/2` is the spelling.

## Known soft spot

The widening-site inventory in stage 3 is the medium-confidence part of this
plan. `coerce_to_kind` / `coerce_int_return` / `merge_if_branches` are
confirmed boundaries, but I have not traced every path by which an Int-Kinded
value can arrive somewhere a Rational is expected. The failure mode is a
mismatched LLVM value reaching codegen — which asserts loudly rather than
miscompiling, so it surfaces as a crash in testing rather than a silent wrong
answer. Budget for finding one or two of these during stage 3 rather than
expecting the list above to be complete.
