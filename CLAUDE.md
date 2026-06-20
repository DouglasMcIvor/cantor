# Intro

This is a very early prototype of an esoteric language named "Cantor".
See docs/design-decisions.md for the current state of the langugage design.

We are currently building out a first prototype, so decisions within that
document may be up for debate if you think they aren't working or need revision -
just let me know what you think and we can decide together.

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


