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
//! has an offset to write at. Output crosses back the same way — either as
//! UTF-8 text bytes (`output_ptr`/`output_len`, the original `Char*` shape)
//! or, for the `Image` convention (docs/design-decisions.md §6), as
//! pre-packed RGBA pixel bytes plus width/height (`output_width`/
//! `output_height`/`output_pixels_ptr`/`output_pixels_len`) — see
//! `event_loop::OutputKind`/`OutputValue` for which is which and why calling
//! the wrong accessor panics rather than reading garbage.
//!
//! Nothing here is wasm-specific enough to need `cfg(target_arch)`: it builds
//! and unit-tests natively, which is the only way most of it gets tested at
//! all.

use std::cell::RefCell;

use crate::{
    deep_copy::LeafShape,
    event_loop::{EventLoop, OutputKind, OutputValue},
};

thread_local! {
    /// The running program. `None` until `init`.
    static PROGRAM: RefCell<Option<EventLoop>> = const { RefCell::new(None) };
    /// Reusable scratch for the UTF-8 `Event` bytes JS writes in. Reused
    /// rather than allocated per call so the host never has to free
    /// anything — there is no `dealloc` export to forget to call.
    static INPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    /// The most recent `step`'s decoded `Output`, kept alive for JS to read
    /// between `step` returning and the next call — which accessor exports
    /// (`output_ptr`/`output_len` vs `output_width`/`output_pixels_ptr`/…)
    /// are meaningful depends on which variant this holds, i.e. on the
    /// compiled program's Output Kind (fixed for the whole run).
    static OUTPUT: RefCell<OutputValue> =
        const { RefCell::new(OutputValue::CharStar(String::new())) };
}

/// Seed the program's `State`, readying it for `step`.
///
/// # Safety
/// Same contract as [`EventLoop::new`]: `seed`/`step` must be the genuine
/// trampolines for a `State` of exactly `n_state_leaves` i64 leaves, and
/// `state_shape` must describe that same `State` Kind. `output_kind` must
/// match `step`'s actual compiled Output Kind.
pub unsafe fn init(
    seed: unsafe extern "C" fn(*mut i64),
    step: unsafe extern "C" fn(*mut i64, *mut i64),
    output_kind: OutputKind,
    n_state_leaves: usize,
    state_shape: LeafShape,
) {
    let program = unsafe { EventLoop::new(seed, step, output_kind, n_state_leaves, state_shape) };
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

    OUTPUT.with(|o| *o.borrow_mut() = output);
}

/// Panic message shared by every accessor below when called against the
/// wrong `OutputValue` variant — a host/program mismatch (e.g. an Image
/// demo's JS glue calling the `Char*` accessors), not a legitimate runtime
/// outcome, so this fails loudly rather than returning a bogus pointer.
fn wrong_accessor(expected: &str) -> ! {
    panic!(
        "cantor_wasm_output_* accessor called for `{expected}` Output, but this program's \
         Output isn't that shape — the JS host and the compiled program disagree about the \
         Output Kind"
    );
}

/// Where the last `step`'s `Output` text bytes start in linear memory —
/// only meaningful when Output is `Char*`.
pub fn output_ptr() -> *const u8 {
    OUTPUT.with(|o| match &*o.borrow() {
        OutputValue::CharStar(s) => s.as_ptr(),
        OutputValue::Image { .. } => wrong_accessor("Char*"),
    })
}

/// How many bytes of `Output` text the last `step` produced — only
/// meaningful when Output is `Char*`.
pub fn output_len() -> usize {
    OUTPUT.with(|o| match &*o.borrow() {
        OutputValue::CharStar(s) => s.len(),
        OutputValue::Image { .. } => wrong_accessor("Char*"),
    })
}

/// The last `step`'s Image Output width — only meaningful when Output is
/// the `Image` convention (docs/design-decisions.md §6).
pub fn output_width() -> u32 {
    OUTPUT.with(|o| match &*o.borrow() {
        OutputValue::Image { width, .. } => *width as u32,
        OutputValue::CharStar(_) => wrong_accessor("Image"),
    })
}

/// The last `step`'s Image Output height — see `output_width`.
pub fn output_height() -> u32 {
    OUTPUT.with(|o| match &*o.borrow() {
        OutputValue::Image { height, .. } => *height as u32,
        OutputValue::CharStar(_) => wrong_accessor("Image"),
    })
}

/// Where the last `step`'s Image Output pixel bytes start in linear
/// memory — row-major, 4 bytes (R, G, B, A) per pixel, ready for
/// `new ImageData(...)` with no further repacking. Only meaningful when
/// Output is the `Image` convention.
pub fn output_pixels_ptr() -> *const u8 {
    OUTPUT.with(|o| match &*o.borrow() {
        OutputValue::Image { pixels_rgba, .. } => pixels_rgba.as_ptr(),
        OutputValue::CharStar(_) => wrong_accessor("Image"),
    })
}

/// How many pixel bytes `output_pixels_ptr` points to (`width * height *
/// 4`) — see `output_pixels_ptr`.
pub fn output_pixels_len() -> usize {
    OUTPUT.with(|o| match &*o.borrow() {
        OutputValue::Image { pixels_rgba, .. } => pixels_rgba.len(),
        OutputValue::CharStar(_) => wrong_accessor("Image"),
    })
}
