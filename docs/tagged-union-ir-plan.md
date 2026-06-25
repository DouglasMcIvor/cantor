# Tagged-Union IR: Implementation Plan

**Status:** planning (as of 2026-06-25)  
**Blocked tests:** 3 `#[ignore]` tests in `tests/codegen/set_ops.rs`  
**Companion solver work:** `src/solver/encode.rs:522` (CVC5 algebraic datatype TODO)

---

## Why this is needed

Cantor's `|` (union) operator can mix sets from different LLVM *kinds* — e.g.
`(Nat * Nat) | Nat` has one arm that is an LLVM struct `{i64, i64}` and one arm
that is a plain `i64`.  There is no single LLVM type that can hold either value
without an explicit tag saying which arm is live.

Currently `set_kind` and `range_kind` in `src/kind.rs` panic with a TODO when
they encounter a mixed-kind `|` union.  This is correct defensive behaviour; the
plan below removes those panics by actually implementing the representation.

Cross-kind unions where **both** arms are scalars (e.g. `Bool | Nat`) already
work — both arms fit in i64 and need no tag.  This plan only concerns unions
that mix a `Kind::Tuple` arm with any non-tuple arm.

---

## Representation

A tagged union `A | B | …` where at least one arm is a Tuple is represented
as an LLVM struct:

```
{ i32 tag, i64 leaf_0, i64 leaf_1, … }
```

- **tag** (field 0): zero-based arm index (arm 0 = leftmost).
- **leaf fields**: enough i64 slots to hold the widest arm.  Every Kind
  serialises to a flat sequence of i64 leaves:
  - `Kind::Int` → 1 leaf (value as-is)
  - `Kind::Bool` → 1 leaf (zero-extended to i64)
  - `Kind::Tuple([K0, K1, …])` → leaves of K0 + leaves of K1 + …
  - `Kind::TaggedUnion(arms)` → 1 + max_leaves leaf (recursive)

For `(Nat * Nat) | Nat`:
- Tuple arm: 2 leaves; Nat arm: 1 leaf → struct is `{ i32, i64, i64 }`.

For `Bool | (Nat * Nat)`:
- Bool arm: 1 leaf; Tuple arm: 2 leaves → struct is `{ i32, i64, i64 }`.

This keeps the struct type simple and avoids byte-array reinterpretation casts.

---

## New `Kind` variant

Add to `src/kind.rs`:

```rust
/// LLVM struct `{ i32 tag, i64… }` — cross-kind union `A | B` where at least
/// one arm is a Tuple.  Arms listed in declaration order (leftmost = index 0).
Kind::TaggedUnion(Vec<Kind>),
```

Two helpers also needed in `kind.rs`:

```rust
/// Number of i64 leaf fields for a Kind (used to size the tagged-union struct).
pub fn leaf_count(kind: &Kind) -> usize { … }

/// Maximum leaf count across all arms of a tagged union.
pub fn tagged_union_leaf_count(arms: &[Kind]) -> usize {
    arms.iter().map(leaf_count).max().unwrap_or(0)
}
```

---

## Implementation steps (in order)

### Step 1 — `Kind::TaggedUnion` + `kind.rs` kind derivation

**Files:** `src/kind.rs`

1. Add the `Kind::TaggedUnion(Vec<Kind>)` variant.
2. Add `leaf_count` and `tagged_union_leaf_count` helpers.
3. In `set_kind`'s `BinOp::Union` arm: instead of panicking when
   `lhs_tuple != rhs_tuple`, flatten all arms and return
   `Kind::TaggedUnion(arms.into_iter().map(set_kind).collect())`.
4. In `range_kind`'s union handler: same — build `Kind::TaggedUnion` instead
   of panicking.
5. Update `compile_items` in `src/codegen/mod.rs` — the match on `param_kinds`
   and return kinds that currently only handles `Kind::Tuple` needs to handle
   `Kind::TaggedUnion` in the same way (struct ABI).

**Tests to write first (TDD):**  These should compile and run after this step
even though we can't yet *use* the tagged union inside the body:
```rust
// main ignores x — just checks compilation succeeds with new LLVM struct param
fn cross_kind_bool_or_tuple_compiles() { jit_src_one_arg("main : Bool | (Nat * Nat) -> Int\nmain(x) = 1", 0) }
fn cross_kind_tuple_or_nat_compiles()  { jit_src_one_arg("main : (Nat * Nat) | Nat -> Int\nmain(x) = 1", 7) }
```
These are exactly the existing `cross_kind_bool_or_tuple_bool_arm` and
`cross_kind_tuple_or_nat_nat_arm` tests; remove their `#[ignore]` when step 1
passes.

---

### Step 2 — LLVM type + codegen infrastructure

**Files:** `src/codegen/mod.rs`

1. Extend `kind_to_llvm_type` for `Kind::TaggedUnion(arms)`:
   ```rust
   Kind::TaggedUnion(arms) => {
       let n = tagged_union_leaf_count(arms);
       let i32t = self.context.i32_type();
       let i64t = self.context.i64_type();
       let mut fields: Vec<BasicTypeEnum> = vec![i32t.into()];
       fields.extend(std::iter::repeat(i64t.into()).take(n));
       self.context.struct_type(&fields, false).into()
   }
   ```

2. Add `build_tagged_union_value(arm_idx, value, arm_kind, all_arms)`:
   Serialises a value into a `{ i32, i64… }` struct.
   - Insert `arm_idx` as i32 into field 0.
   - Walk `arm_kind` leaves and insert each i64 into fields 1..N.
   - Zero-extend `Bool` leaves to i64.
   - For `Tuple` arms, extract each element and recurse.

3. Add `extract_tagged_union_arm(tagged, arm_idx, arm_kind, all_arms)`:
   Deserialises arm `arm_idx` from a tagged-union struct.
   - For scalar arms: extract field 1 as i64 (truncate to i1 for Bool).
   - For tuple arms: extract fields 1..K and reassemble a struct.

4. Add `extract_tag(tagged) -> IntValue<'ctx>`:
   Extract field 0 (i32) from a tagged-union struct.

5. Extend `declare_function` — the match on `return_kind` that currently
   handles `Kind::Tuple(…)` needs a parallel arm for `Kind::TaggedUnion(…)`.

6. Extend `compile_function_body` / `compile_block_body` — the parameter loop
   currently handles `Kind::Tuple`; add:
   ```rust
   } else if matches!(kind, Kind::TaggedUnion(_)) {
       (llvm_param, kind.clone())
   ```

---

### Step 3 — membership check for tagged unions

**Files:** `src/codegen/membership.rs`, `src/codegen/expr.rs`

The existing `compile_membership` takes an `IntValue<'ctx>` — a scalar.
For `Kind::TaggedUnion` values the param is a struct; `lv.into_int_value()`
would panic.

Changes needed:

1. In `compile_binop`'s `BinOp::In` / `BinOp::NotIn` handler in `expr.rs`,
   **before** calling `compile_membership`, check if `lk` is
   `Kind::TaggedUnion`:
   ```rust
   if let Kind::TaggedUnion(ref arms) = lk {
       let pred = self.compile_tagged_union_membership(lv, arms, rhs)?;
       // handle NotIn …
       return Ok((pred.into(), Kind::Bool));
   }
   ```

2. Add `compile_tagged_union_membership(val, arms, set_expr)` in
   `membership.rs`:
   - Extract `tag = extract_tag(val)` as i32 (or widen to i64 for comparison).
   - Find which arm index `i` corresponds to `set_expr`:
     - If `set_expr` is exactly `A * B` (tuple), compare `set_kind(set_expr)`
       against each arm's kind; the matching arm index is `i`.
     - If `set_expr` is a named scalar set (e.g. `Nat`), find the scalar arm.
   - Return `(tag == i) as i1`.
   - For now: only support set expressions that exactly match one arm by kind.
     Anything more complex can return `Err(CompileError::Internal("…not yet
     supported…"))`.

After this step the third `#[ignore]` test (`cross_kind_tuple_arm_domain_membership_check`) can be un-ignored.

---

### Step 4 — constructing tagged-union return values

**Files:** `src/codegen/mod.rs` (`wrap_return_value`)

Currently, if a function's declared range is `Kind::TaggedUnion` but the body
produces `Kind::Tuple` or `Kind::Int`, there is an LLVM type mismatch.  Fix
this by extending `wrap_return_value` (and the return-building logic in
`compile_function_body`) to call `build_tagged_union_value` when the body kind
matches one arm of the expected tagged-union return kind.

Concretely: in `compile_function_body`, after compiling the body, if
`ret_kind == Kind::TaggedUnion(arms)` and `body_kind != Kind::TaggedUnion(…)`,
search `arms` for one whose kind matches `body_kind`, and wrap the value.

This is the last piece required to make `main : Nat -> (Nat * Nat) | Nat` and
similar range-position unions compile correctly.

---

### Step 5 — if/then/else across tagged-union arms

**Files:** `src/codegen/expr.rs` (`compile_if`)

Currently `compile_if` builds a phi node assuming both branches have the same
LLVM type.  For:
```cantor
f : Nat -> (Nat * Nat) | Nat
f(x) = if x > 0 then (x, x) else x
```
the `then` branch yields `Kind::Tuple` and the `else` branch yields `Kind::Int`.
Both need to be wrapped into the same `Kind::TaggedUnion` struct before the phi.

Extend the coercion logic in `compile_if`: when the result type should be
`Kind::TaggedUnion(arms)`, wrap each branch value before merging.

---

### Step 6 — solver support (CVC5 algebraic datatype)

**Files:** `src/solver/encode.rs`

There is already a detailed TODO block at line 522 describing Option A (CVC5
algebraic datatype sort).  The high-level steps from that comment:

1. In `set_sort`, detect cross-kind unions and build a CVC5 datatype sort with
   one constructor per arm.
2. Teach `membership_constraint` to emit `ApplyTester`/`ApplySelector` terms
   when the term's sort `.is_datatype()`.
3. Update counterexample extraction to decode and display the arm.

This step is independent of codegen steps 1–5 and can proceed in parallel.

---

## Test plan (TDD order)

| Step | Tests to add | Expected outcome |
|------|-------------|-----------------|
| 1    | `cross_kind_bool_or_tuple_bool_arm`, `cross_kind_tuple_or_nat_nat_arm` (remove `#[ignore]`) | compile + body=1 runs |
| 3    | `cross_kind_tuple_arm_domain_membership_check` (remove `#[ignore]`) | tag check returns correct 0/1 |
| 4    | new: `main : Nat -> (Nat*Nat)\|Nat; main(x) = (x, x+1)` with trampoline helper | tuple arm returned correctly |
| 4    | new: `main : Nat -> (Nat*Nat)\|Nat; main(x) = x` with trampoline helper | scalar arm returned correctly |
| 5    | new: `if` expression branching across tuple and scalar arms | correct arm dispatched |
| 6    | new solver tests for `f : (Nat*Nat)\|Nat -> Int` | proved / counterexample |

The trampoline tests in step 4 will need a new helper
`jit_src_one_arg_to_tuple(src, arg) -> Vec<i64>` that calls `cantor_main_into`
via an additional trampoline that accepts one i64 argument.  Alternatively,
write zero-arg tests that hard-code the argument.

---

## Files touched summary

| File | Change |
|------|--------|
| `src/kind.rs` | Add `Kind::TaggedUnion`, `leaf_count`, `tagged_union_leaf_count`; update `set_kind`, `range_kind` |
| `src/codegen/mod.rs` | `kind_to_llvm_type`, `declare_function`, `compile_function_body`, `compile_block_body`, `wrap_return_value`; new `build_tagged_union_value`, `extract_tagged_union_arm`, `extract_tag` |
| `src/codegen/expr.rs` | `compile_binop` (BinOp::In dispatch), `compile_if` (cross-arm phi) |
| `src/codegen/membership.rs` | New `compile_tagged_union_membership` |
| `src/solver/encode.rs` | `set_sort` + `membership_constraint` for datatype sort (step 6) |
| `tests/codegen/set_ops.rs` | Remove `#[ignore]` from 3 tests; add new range/if tests |
| `tests/solver/…` | New solver tests for cross-kind union domains (step 6) |

---

## What is explicitly NOT in scope

- `match` expressions (discriminating on tagged unions syntactically) — that
  is a parser + codegen feature on top of the IR foundation built here.
- Cross-kind unions in set-literal position (`{(1,2), 3}`) — deferred.
- Nested tagged unions (`(A * B) | (C * D * E)`) — the leaf-count approach
  handles these mechanically, but the tests don't cover them yet.
- `Kind::Union` (disjoint `+`) still uses i64 Stage-2 wire type.  Its Stage-3
  upgrade to tagged-union IR is a separate item.
