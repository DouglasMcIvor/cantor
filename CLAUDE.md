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

# Development process

This codebase is growing! Which means our development requires a bit more care and discipline going forward.

## Design process

1. I strongly appreciate being told that I'm wrong, particularly with succinct counter examples! That's how I learn! Some LLMs can be overly syncophantic at times, don't feel the need to keep me happy!
2. In a similar vein: try not to make assumptions about things if you are unsure. I like to know how confident you feel whenyou tell me something. I find someone jumping to a conclusion that I can immediately tell is wrong, and then stating it _with confidence_ quite offputting. Being wrong is absolutely fine! What I don't like is someone being unjustifiably confident or unjustifiably unsure. (Perhaps you can tell that I'm a fan of the Bayesian approach to probability? :-P)

## Code changes

1. If a suggested change is very large then consider suggesting to the user that it is made in multiple steps.
0. **Unimplemented paths must fail loudly, never silently.**
   When a feature is only partially implemented, every unimplemented code path must
   panic (or return a `CompileError`) with a clear "not yet implemented / TODO: <feature>"
   message.  A wildcard match arm that silently falls back to a plausible-looking default
   (e.g. `_ => Kind::Int` for an unhandled union variant) creates "accidentally passing"
   tests that mask missing functionality and give false confidence.  The same principle
   applies to tests: a test whose inputs never exercise the unimplemented path is not a
   real test of that path — pair each `#[ignore]` with a comment explaining *why* it
   fails and what needs to be implemented for it to pass.
2. One natural way to break down some large changes could be parser/codegen/solver changes as three distinct steps.
3. Temporary short cuts are fine and to be expected, but be explicit to the user about any short cuts you have taken so that they know to address them in future! A TODO that sneaks in and isn't addressed in a timely manner may cost us later on.
4. All temporary short cuts or hacks need be marked clearly with a TODO comment so they are easy to discover in the future
5. All code changes should be concluded with both new CLI end-to-end tests and documentation updates.
6. Use TDD where sensible! If we are introducing new functionality and we are very confident on the interface it exposes then it makes sense to write the tests first and watch them go incrementally green over each step of the change.

## Documentation updates

1. Documentation should be updated in single commits to ensure it always remains internally consistent.
2. Remember that Cantor has no types!!! It is shockingly easy for one of us to accidentally use the word "type" when describing a Cantor feature, and for the other of us to not even notice until days later! We should tell each other off if we let the word "type" slip into discussions about Cantor features. (Using it to discuss the rust implemenation otoh is obviously fine though).

