# Intro

This is a very early prototype of an esoteric language named "Cantor".
See docs/design-decisions.md for the current state of the langugage design.

We are currently building out a first prototype, so decisions within that
document may be up for debate if you think they aren't working or need revision -
just let me know what you think and we can decide together.

# Code organisation

**Test structure mirrors source structure.**
`tests/solver/` mirrors `src/solver/`, `tests/parser/` would mirror `src/parser/`, and so on.
The entry point (e.g. `tests/solver.rs`) uses `#[path]` attributes to wire up the subdirectory
since integration test roots don't follow the standard module-path rule.

**Keep files under 1000 lines.**
If a source or test file grows beyond that, flag it and propose a pure refactor commit to split
it before adding more features. The split should have no behaviour changes and all tests must
still pass — the commit message should say "refactor" so it's easy to skip in blame.

# Design principles

These are settled decisions that should be applied consistently across the
compiler — raise it if you think a situation warrants an exception.

**The compiler never silently assumes anything that isn't proved.**
If the SMT solver cannot establish a claim (timeout, unsupported syntax, etc.),
the result must be `Unknown` — not a silent pass that treats the claim as true.
The only way to assert an unproved fact is for the developer to write an
explicit `assume` statement in source code (unconditional trust) or `assert`
(graduated: proved → elided, unknown → runtime check, always-false → error).
This applies everywhere: range checks, `require` obligations, loop invariant
inductive steps, built-in domain constraints, and any future verification
the compiler adds.


