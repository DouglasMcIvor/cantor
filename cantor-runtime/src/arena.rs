//! Bump-style object arena backing every heap allocation in this crate
//! (`lib.rs`, `bigint.rs`). Each `Cantor*` struct is `Box`-allocated as
//! before, but instead of leaking via `Box::into_raw` the box is handed to
//! the current arena, which keeps it alive (type-erased) until `reset()`
//! runs. `reset()` drops every object registered since the last reset —
//! including their own internal heap data (Arrow buffers, `BigInt` digit
//! vecs, etc.), which a plain bump allocator over raw bytes would not do.
//!
//! `event_loop::drive_event_loop` wires this up at the per-step boundary via
//! `swap`: swap in a fresh arena as "current" (so the deep copy in
//! `deep_copy.rs` allocates into it), copy every reachable `State` leaf into
//! that fresh arena, *then* drop the arena `swap` handed back — which still
//! holds every allocation from the step that just ran, everything not
//! copied included.

use std::any::Any;
use std::cell::RefCell;

#[derive(Default)]
pub struct Arena {
    objects: Vec<Box<dyn Any>>,
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    /// Box `val`, register it with this arena, and return the raw pointer.
    /// The pointer stays valid until this `Arena` is dropped or replaced —
    /// moving a `Box` (e.g. when `objects` grows) relocates the pointer
    /// *wrapper*, never the pointee, so returned pointers are stable.
    pub fn alloc<T: 'static>(&mut self, val: T) -> *mut T {
        let mut boxed = Box::new(val);
        let ptr: *mut T = &mut *boxed;
        self.objects.push(boxed);
        ptr
    }
}

thread_local! {
    static CURRENT: RefCell<Arena> = RefCell::new(Arena::new());
}

/// Allocate `val` in the current arena, returning it as a pointer-as-i64 —
/// the same representation `Box::into_raw(...) as i64` produced before.
pub fn alloc<T: 'static>(val: T) -> i64 {
    CURRENT.with(|c| c.borrow_mut().alloc(val)) as i64
}

/// Drop every object allocated in the current arena since the last reset,
/// running each object's real destructor (freeing Arrow buffers, `BigInt`
/// digit vecs, etc., not just the outer `Cantor*` wrapper struct).
///
/// # Safety
/// Any pointer previously returned by `alloc` and still in use (e.g. a
/// `State` leaf that must survive into the next event-loop step) must be
/// deep-copied into a fresh arena *before* calling this — `reset` has no
/// way to know which outstanding pointers are still reachable.
#[allow(dead_code)] // exercised directly by tests; production code goes through `swap`
pub fn reset() {
    CURRENT.with(|c| *c.borrow_mut() = Arena::new());
}

/// Install `fresh` as the current arena and return the arena it replaces.
/// The caller keeps the returned `Arena` alive for as long as pointers into
/// it are still being read (e.g. while deep-copying `State` out of it) —
/// once it's dropped, every object it holds is dropped for real.
pub fn swap(fresh: Arena) -> Arena {
    CURRENT.with(|c| std::mem::replace(&mut *c.borrow_mut(), fresh))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Canary(Rc<AtomicUsize>);

    impl Drop for Canary {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn reset_drops_registered_objects() {
        let drops = Rc::new(AtomicUsize::new(0));
        let before = drops.load(Ordering::SeqCst);

        for _ in 0..5 {
            alloc(Canary(drops.clone()));
        }
        assert_eq!(drops.load(Ordering::SeqCst), before, "not dropped yet");

        reset();
        assert_eq!(
            drops.load(Ordering::SeqCst),
            before + 5,
            "reset must drop all 5"
        );
    }

    #[test]
    fn alloc_returns_a_usable_pointer() {
        let ptr = alloc(42i64) as *mut i64;
        assert_eq!(unsafe { *ptr }, 42);
        unsafe {
            *ptr = 7;
        }
        assert_eq!(unsafe { *ptr }, 7);
        reset();
    }
}
