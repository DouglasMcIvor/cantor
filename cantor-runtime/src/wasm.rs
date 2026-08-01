//! The embedding ABI a `cantor build --target wasm32` module exposes to its
//! JavaScript host — the browser counterpart of `event_loop`'s stdin loop.
//!
//! A browser can't hand the program a blocking `stdin`, so the roles invert:
//! instead of Cantor owning the read loop, JS owns it and calls in one
//! `Event` at a time (`step`), with the program's `State` parked in
//! `PROGRAM` between calls. The generated driver (`codegen::aot`) wraps each
//! function below in a `#[unsafe(no_mangle)] extern "C"` shim so it lands in
//! the wasm module's export table.
//!
//! Strings cross the boundary as UTF-8 bytes in the wasm module's own linear
//! memory, which JS can read and write directly as a `Uint8Array`. Passing
//! one in takes two calls — `input_buffer(len)` to get somewhere to write,
//! then `step(len)` — because JS cannot write into linear memory until it
//! has an offset to write at.
//!
//! Nothing here is wasm-specific enough to need `cfg(target_arch)`: it builds
//! and unit-tests natively, which is the only way most of it gets tested at
//! all.

use std::cell::RefCell;

use crate::{deep_copy::LeafShape, event_loop::EventLoop};

thread_local! {
    /// The running program. `None` until `init`.
    static PROGRAM: RefCell<Option<EventLoop>> = const { RefCell::new(None) };
    /// Reusable scratch for the UTF-8 `Event` bytes JS writes in. Reused
    /// rather than allocated per call so the host never has to free
    /// anything — there is no `dealloc` export to forget to call.
    static INPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    /// The most recent `Output`, as UTF-8 bytes, kept alive for JS to read
    /// between `step` returning and the next call.
    static OUTPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

/// Seed the program's `State`, readying it for `step`.
///
/// # Safety
/// Same contract as [`EventLoop::new`]: `seed`/`step` must be the genuine
/// trampolines for a `State` of exactly `n_state_leaves` i64 leaves, and
/// `state_shape` must describe that same `State` Kind.
pub unsafe fn init(
    seed: unsafe extern "C" fn(*mut i64),
    step: unsafe extern "C" fn(*mut i64, *mut i64),
    n_state_leaves: usize,
    state_shape: LeafShape,
) {
    let program = unsafe { EventLoop::new(seed, step, n_state_leaves, state_shape) };
    PROGRAM.with(|p| *p.borrow_mut() = Some(program));
}

/// Reserve `len` bytes for the next `Event` and return where to write them.
///
/// The pointer stays valid until the next `input_buffer` call, which is the
/// only thing that can resize the buffer out from under it — so the host's
/// required sequence is strictly `input_buffer(len)`, write exactly `len`
/// bytes, `step(len)`.
pub fn input_buffer(len: usize) -> *mut u8 {
    INPUT.with(|b| {
        let mut b = b.borrow_mut();
        b.clear();
        b.resize(len, 0);
        b.as_mut_ptr()
    })
}

/// Run the `len` UTF-8 bytes now in the input buffer through the program as
/// one `Event`, leaving its `Output` for `output_ptr`/`output_len` to read.
///
/// Panics — which traps the wasm module, surfacing in the host as an
/// exception rather than a silently wrong answer — if `init` has not run or
/// if the host wrote bytes that are not valid UTF-8.
pub fn step(len: usize) {
    let event = INPUT.with(|b| {
        String::from_utf8(b.borrow()[..len].to_vec())
            .expect("host wrote invalid UTF-8 into the Cantor event buffer")
    });

    let output = PROGRAM.with(|p| {
        p.borrow_mut()
            .as_mut()
            .expect("cantor_wasm_step called before cantor_wasm_init")
            .step(&event)
    });

    OUTPUT.with(|o| *o.borrow_mut() = output.into_bytes());
}

/// Where the last `step`'s `Output` bytes start in linear memory.
pub fn output_ptr() -> *const u8 {
    OUTPUT.with(|o| o.borrow().as_ptr())
}

/// How many bytes of `Output` the last `step` produced.
pub fn output_len() -> usize {
    OUTPUT.with(|o| o.borrow().len())
}
