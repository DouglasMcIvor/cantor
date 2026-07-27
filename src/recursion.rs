//! A depth backstop for the two compiler passes that expand a named set's
//! *definition* while walking an expression (`kind::set_kind` and
//! `solver::membership::membership_constraint`).
//!
//! Both are structurally recursive over a finite expression tree except at
//! one point: resolving a `Var` to its `NameDef` and recursing into that
//! definition's value. A cycle in the definitions therefore makes them
//! recurse forever. `semantics::wellfounded` exists to reject exactly that
//! before either pass runs, and this module is not a second implementation
//! of that check — it's the guard rail behind it.
//!
//! **Why bother, given the check already exists?** Because of how the check
//! failed once. `wellfounded::build_raw_dep_graph` narrowed its dependency
//! graph on an assumption about which definitions `set_kind` recurses into;
//! `set_kind` later changed, the assumption quietly became false, and every
//! recursive `distinct` definition aborted the compiler with a stack
//! overflow. A stack overflow is the one failure mode that escapes this
//! project's "unimplemented paths must fail loudly" rule entirely: the
//! process aborts, so there is no panic to catch, no span, no message, and
//! nothing a test can assert on beyond the absence of an exit code. Turning
//! it into an ordinary `CompileError::Ice` costs one integer compare per
//! definition expansion and makes the *next* instance of that class a
//! reportable bug instead of a crash.
//!
//! Deliberately not a general "am I too deep" counter on every recursive
//! function in the compiler: it guards the specific step that can revisit a
//! definition it has already visited. A program with genuinely 512-deep
//! nesting of distinct named sets is not something Cantor supports today
//! for unrelated reasons, so the limit doesn't need to be tunable.

use std::cell::Cell;

use crate::error::CompileError;

/// Maximum number of nested *definition expansions*.
///
/// Bounded from **above** by the stack, not by taste: the guard is worthless
/// if the stack runs out before the counter trips. Measured by bisection on
/// `A = A * A` (`tests/kind_tests.rs`), a debug build overflows a 2 MiB test
/// thread somewhere between 112 and 120 levels — call it ~17 KiB of stack per
/// level for `set_kind` → `binop_kind` → `set_kind`. 64 leaves comfortable
/// margin under the tightest configuration the compiler runs in (test threads
/// get 2 MiB, the main thread 8 MiB, and release frames are smaller than debug
/// ones — so every other configuration has more headroom, not less).
///
/// Bounded from **below** by real programs, which is barely a constraint at
/// all: this counts *nesting* of definition expansions, so `Foo = Bar * Baz`
/// where both are three-deep alias chains reaches depth 4, not 6. Nothing
/// hand-written comes close to 64.
///
/// If you raise this, re-run the bisection. The `cyclic_*` tests in
/// `tests/kind_tests.rs` fail by aborting the whole test binary — not by a
/// normal assertion failure — if the limit ever climbs back over the stack
/// ceiling, which is the failure mode this constant exists to prevent.
const MAX_DEFINITION_DEPTH: u32 = 64;

thread_local! {
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// Decrements the shared depth counter when dropped, so the count unwinds
/// correctly however the guarded frame exits — including the `?` early
/// returns that both guarded functions are full of.
#[derive(Debug)]
pub struct DepthGuard;

impl Drop for DepthGuard {
    fn drop(&mut self) {
        DEPTH.with(|d| d.set(d.get() - 1));
    }
}

/// Enter one level of definition expansion, or report a compiler bug if the
/// limit has been reached. Hold the returned guard for as long as the
/// recursive call is in progress:
///
/// ```text
/// let _guard = recursion::enter_definition(&sym.0)?;
/// set_kind(&def.value, name_defs)
/// ```
///
/// `Ice` rather than `Diagnostic`/`Unsupported` is deliberate: reaching this
/// point means `semantics::wellfounded` passed a definition cycle through,
/// which is a bug in the compiler, not a mistake in the user's program. The
/// message names the definition being expanded, since that's the entry point
/// into the cycle and the one piece of information a stack overflow can't
/// give you.
pub fn enter_definition(name: &str) -> Result<DepthGuard, CompileError> {
    DEPTH.with(|d| {
        let depth = d.get();
        if depth >= MAX_DEFINITION_DEPTH {
            return Err(CompileError::ice(format!(
                "exceeded {MAX_DEFINITION_DEPTH} nested set-definition expansions while \
                 resolving `{name}` — almost certainly a cycle in the set definitions that \
                 `semantics::wellfounded` should have rejected first (see src/recursion.rs)"
            )));
        }
        d.set(depth + 1);
        Ok(DepthGuard)
    })
}

/// `enter_definition` for a caller with no `CompileError` in its return
/// type. Same counter, same limit; panics instead of returning, which is
/// still infinitely more debuggable than a stack overflow (a panic has a
/// message, a Rust location, and a backtrace).
pub fn enter_definition_or_panic(name: &str) -> DepthGuard {
    match enter_definition(name) {
        Ok(guard) => guard,
        Err(e) => panic!("{e}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn depth_unwinds_when_guards_drop() {
        // The counter is thread-local and every test runs on its own thread,
        // so this starts from zero regardless of what else is running.
        {
            let _a = enter_definition("A").expect("first level must be allowed");
            let _b = enter_definition("B").expect("second level must be allowed");
            assert_eq!(DEPTH.with(|d| d.get()), 2);
        }
        assert_eq!(
            DEPTH.with(|d| d.get()),
            0,
            "guards must decrement on drop, or one deep-but-finite file would \
             poison every later one on the same thread"
        );
    }

    #[test]
    fn exceeding_the_limit_is_an_ice_naming_the_definition() {
        let mut guards = Vec::new();
        for _ in 0..MAX_DEFINITION_DEPTH {
            guards.push(enter_definition("Deep").expect("under the limit"));
        }
        let err = enter_definition("Cyclic").expect_err("at the limit");
        assert!(err.is_ice(), "must be an Ice, got {err:?}");
        assert!(
            err.to_string().contains("Cyclic"),
            "must name the definition being expanded: {err}"
        );
    }
}
