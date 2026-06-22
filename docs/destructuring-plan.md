# Destructuring assignment — implementation plan

## Agreed syntax

```
x, y = (-3, 4)              -- immutable, no constraints
x : Int, y : Nat = (-3, 4) -- immutable, per-element constraints
x, y : Int * Nat = (-3, 4) -- immutable, tuple-level constraint (normalises to same)
mut a : Int, b : Nat = (-3, 4) -- all bindings mutable (mut applies to whole pattern)
a, b := (-4, 5)             -- reassignment of existing mutables
```

Parens around the RHS tuple are required (consistent with tuple literal syntax elsewhere).
Parens around the LHS pattern are *not* required — the LHS grammar is restricted enough
that `x, y` unambiguously signals a destructure.

`mut` applies to all bindings in the pattern (keep it simple for v0; revisit if needed).

---

## Step 1 — AST (`src/ast.rs`)

Add a small helper struct and three new `Stmt` variants after `Assign`:

```rust
/// One binding in a destructuring pattern.
pub struct DestructBinding {
    pub name: Symbol,
    pub constraint: Option<Expr>,  // per-element constraint, e.g. `: Int`
}

// In Stmt:
DestructLet {
    bindings: Vec<DestructBinding>,
    tuple_constraint: Option<Expr>,  // from `x, y : Int * Nat` form; None for per-element form
    value: Expr,
    span: Span,
},
DestructMutLet {
    bindings: Vec<DestructBinding>,
    tuple_constraint: Option<Expr>,
    value: Expr,
    span: Span,
},
DestructAssign {
    names: Vec<Symbol>,  // no constraints — must already be declared
    value: Expr,
    span: Span,
},
```

Also update `collect_loop_modified_rec` to visit the new variants (insert all names for
`DestructMutLet` and `DestructAssign`).

---

## Step 2 — Parser (`src/parser/mod.rs`)

Detection uses the existing 2-token lookahead (`peek()` = tok0, `peek2()` = tok1):

| peek0  | peek1  | action                        |
|--------|--------|-------------------------------|
| `Ident`| `,`    | destructuring let/reassign    |
| `Mut`  | `Ident`| then check tok2 == `,`        |

Add two new match arms in `parse_stmt`, before the existing `Ident` arms:

```
Token::Ident(_) if self.peek2() == &Token::Comma  =>  parse_destruct_let_or_assign
Token::Mut      (existing arm, extend it)          =>  detect comma after ident → parse_destruct_mut_let
```

### `parse_destruct_binding_list` helper

```
loop:
  name = expect_ident()
  constraint = if peek() == Colon { advance(); Some(parse_set_expr()) } else { None }
  push DestructBinding { name, constraint }
  if peek() != Comma { break }
  advance()   // consume comma
```

### After the binding list, dispatch on next token:

- `:=` → `DestructAssign` (validate: all `constraint` fields must be `None`, error otherwise)
- `:` → tuple-constraint form: parse `parse_set_expr()`, then `=`, then value → `DestructLet`
- `=` → per-element form: parse value → `DestructLet` (constraints already in bindings)

### `mut` arm

After consuming `Mut`, peek at `peek2()`: if it's `,` use the same parse path above
and emit `DestructMutLet`; otherwise fall through to the existing single-binding `MutLet` path.

> Note: the parser currently only has 2-token lookahead. For `mut a, b = ...` we need
> `tok0=Mut tok1=Ident tok2=Comma`. Add a `peek3()` helper (mirrors `peek2`) to support this,
> or speculatively consume `Mut` before checking — the existing `Mut` arm already advances first,
> so after `advance()` we have `peek()=Ident, peek2()=Comma` which is sufficient.

---

## Step 3 — Solver (`src/solver/`)

The place to hook in is wherever `Stmt::Let` and `Stmt::MutLet` are encoded (currently
`src/solver/encode.rs` or `src/solver/mod.rs` — confirm at time of impl).

For **`DestructLet` / `DestructMutLet`**:

1. Encode the RHS expression into an SMT term `rhs`.
2. For each `binding[i]`:
   - Introduce a fresh SMT variable `vi`.
   - Assert `vi = rhs.i` (projection — reuse the existing `TupleProj` encoding).
   - If `binding.constraint` is `Some(c)`: assert `vi ∈ c` (same as `Let` membership check).
3. If `tuple_constraint` is `Some(tc)`: assert `rhs ∈ tc` instead of per-element checks
   (the solver already knows how to decompose `Int * Nat` membership).
4. Add all names to the solver scope (immutable or mutable depending on variant).

For **`DestructAssign`**:

- Same as above but update existing SMT variables rather than introducing new ones.
- Validate that each name is in scope and was declared `mut` (error if not — same check
  as for `Stmt::Assign`).

---

## Step 4 — Codegen (`src/codegen/`)

Locate where `Stmt::Let` / `Stmt::MutLet` / `Stmt::Assign` are lowered to LLVM IR
(currently `src/codegen/expr.rs` or `src/codegen/mod.rs`).

For **`DestructLet` / `DestructMutLet`**:

1. Codegen the RHS once into a temporary.
2. For each `binding[i]`, extract element `i` from the temporary (reuse the `TupleProj`
   extraction path) and store it under the binding's name.
3. For `DestructMutLet`, allocate `alloca`-backed storage just like `MutLet`.

For **`DestructAssign`**:

- Extract each element from the RHS temporary and write to the existing `alloca` for
  each name (same store path as `Stmt::Assign`).

---

## Step 5 — Tests

Add to `tests/cantor_files/`:

```
destructure_basics.cantor   -- immutable, per-element constraints, smoke test
destructure_typed.cantor    -- tuple-constraint form `x, y : Int * Nat = ...`
destructure_mut.cantor      -- mut pattern + reassignment
destructure_bad.cantor      -- expect error: reassign immutable, wrong arity, etc.
```

Add corresponding entries in `tests/cli_tests.rs` (mirrors existing tuple test style).
Add solver-level unit tests in `tests/solver/destructuring.rs` and wire via `#[path]`
in `tests/solver.rs`.

---

## Open questions / deferred

- **Mixed mutability**: `mut a, b = ...` where only `a` is mutable. Deferred; current plan
  makes all bindings mutable when `mut` is present.
- **Nested destructuring**: `(x, (y, z)) = ...`. Deferred to a later iteration.
- **Top-level destructuring** (`NameDef` / `FunctionDef` level). Not in v0 — stmts only.
- **`_` wildcard**: `x, _ = (1, 2)` — ignore second element. Easy add-on once basics work.
