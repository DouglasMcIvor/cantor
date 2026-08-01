//! MVP IO event loop (docs/design-decisions.md §6) — shared by the JIT
//! (`cantor run`, main.rs) and AOT (`cantor build`, `src/codegen/aot.rs`)
//! backends. Only `drive_event_loop` differs between the two call sites:
//! JIT resolves `seed`/`step` via an `ExecutionEngine` lookup, AOT gets
//! them as ordinary statically-linked `extern "C"` function pointers — the
//! loop body itself, and every value encode/decode helper below, is
//! identical either way.

use std::io::BufRead;

use crate::{
    arena, cantor_bigint_to_i64, cantor_vec_builder_finish_i64, cantor_vec_builder_new_i64,
    cantor_vec_builder_push_i64, cantor_vec_get_i64, cantor_vec_len_i64,
    deep_copy::{self, LeafShape},
};

/// Which Output convention an event-loop `main` uses (docs/design-
/// decisions.md §6) — `EventLoop`/`drive_event_loop`/`wasm` all decode the
/// flat leaf buffer accordingly. `cantor run`/native `cantor build` only
/// ever construct `CharStar` (`codegen::aot::build_executable`'s guard);
/// `Image` is wasm32-only, since there's no terminal renderer for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputKind {
    /// `Char*` — one leaf (a `Vector(Char)` pointer).
    CharStar,
    /// `Nat * Nat * Unsigned32*` — width, height, row-major pixels packed
    /// one `0xRRGGBBAA` per element — three leaves.
    Image,
}

impl OutputKind {
    /// How many flat i64 leaves this Output shape occupies at the front of
    /// `cantor_step`'s output buffer, before `State`'s own leaves — mirrors
    /// `codegen::wire::leaf_count` for exactly these two shapes.
    pub fn leaf_count(self) -> usize {
        match self {
            OutputKind::CharStar => 1,
            OutputKind::Image => 3,
        }
    }
}

/// A decoded event-loop `main` Output — fully owned Rust memory, safe to
/// keep around after the arena that backed its source leaves during the
/// `step` call has been swapped out and dropped (see `EventLoop::step`'s
/// doc comment: decoding happens *before* that drop, exactly like the
/// pre-existing `format_char_vector` call it generalizes).
#[derive(Debug, Clone)]
pub enum OutputValue {
    CharStar(String),
    Image {
        width: i64,
        height: i64,
        /// Row-major pixels, 4 bytes each (R, G, B, A in that order) — the
        /// byte order a browser `ImageData`/canvas expects directly, so the
        /// wasm host (`web/cantor.js`) can hand this straight to
        /// `new ImageData(...)` with no further repacking.
        pixels_rgba: Vec<u8>,
    },
}

/// Decode `leaves` (exactly `kind.leaf_count()` of them) into an owned
/// `OutputValue` — see `OutputValue`'s doc comment for why this must run
/// before the arena swap that ends a `step` call, not after.
fn decode_output(kind: OutputKind, leaves: &[i64]) -> OutputValue {
    match kind {
        OutputKind::CharStar => OutputValue::CharStar(format_char_vector(leaves[0])),
        OutputKind::Image => {
            let width = cantor_bigint_to_i64(leaves[0]);
            let height = cantor_bigint_to_i64(leaves[1]);
            let pixels_ptr = leaves[2];
            let len = cantor_vec_len_i64(pixels_ptr);
            let mut pixels_rgba = Vec::with_capacity(len as usize * 4);
            for i in 0..len {
                // Vector(Unsigned32) elements are zero-extended into the i64
                // Arrow slot (codegen/expr_vec.rs's vec_builder_fns) — the
                // low 32 bits are the real 0xRRGGBBAA value.
                let px = cantor_vec_get_i64(pixels_ptr, i) as u32;
                pixels_rgba.push((px >> 24) as u8);
                pixels_rgba.push((px >> 16) as u8);
                pixels_rgba.push((px >> 8) as u8);
                pixels_rgba.push(px as u8);
            }
            OutputValue::Image {
                width,
                height,
                pixels_rgba,
            }
        }
    }
}

/// Build a `Char*` (heap-allocated Arrow-backed vector) from a Rust `&str`,
/// one element per Unicode scalar value — the same runtime representation
/// JIT'd/AOT-compiled Cantor code itself builds array literals into.
pub fn encode_char_star(s: &str) -> i64 {
    let builder = cantor_vec_builder_new_i64();
    for c in s.chars() {
        cantor_vec_builder_push_i64(builder, c as i64);
    }
    cantor_vec_builder_finish_i64(builder)
}

/// The synthetic final `Event` fed to an event-loop `main` when its input
/// stream ends: codepoint 4 (ASCII EOT, the traditional Ctrl-D "end of
/// transmission" control character — not U+2404 ␄, which is a printable
/// *display glyph* for EOT and could theoretically appear in real input).
/// docs/design-decisions.md §6.
pub const EOT_EVENT: &str = "\u{4}";

/// Decode a `Char` leaf (zero-extended to i64, same convention as
/// `Unsigned32`) into its display form — the actual character, not the
/// bare codepoint. Only valid Unicode scalar values can ever reach here:
/// `char(n)` proves it once at construction, so `char::from_u32` is
/// infallible.
pub fn format_char(word: i64) -> String {
    let v = word as u32;
    let c = char::from_u32(v)
        .unwrap_or_else(|| panic!("ICE: Char leaf {v} is not a valid Unicode scalar"));
    format!("{c}")
}

/// Decode a `Char*` (`Vector(Char)`) pointer-as-i64 into its text.
pub fn format_char_vector(vec_ptr: i64) -> String {
    let len = cantor_vec_len_i64(vec_ptr);
    (0..len)
        .map(|i| {
            let cp = cantor_vec_get_i64(vec_ptr, i) as u32;
            char::from_u32(cp)
                .unwrap_or_else(|| panic!("ICE: Char* element {cp} is not a valid Unicode scalar"))
        })
        .collect::<String>()
}

/// Drive an event-loop `main` (`Char* * S -> Char* * S`) against `stdin`,
/// one line per `Event`, until `stdin` closes — at which point it feeds one
/// final synthetic `Event` (`encode_eot_event`) and terminates
/// unconditionally, regardless of the `State` that final call returns.
///
/// `seed`/`step` are the compiled program's `cantor_initial_state`/
/// `cantor_step` trampolines (docs/design-decisions.md §6); `n_state_leaves`
/// is `State`'s Kind-leaf count, a compile-time-known constant the caller
/// already has (`count_kind_leaves(state_kind)`). `state_shape` is the same
/// `State` Kind's arena deep-copy shape (`codegen::wire::state_leaf_shape`,
/// built once by the compiler — see `deep_copy.rs`'s module doc). `State` is
/// never formatted here — it's opaque, just copied between calls as a flat
/// i64 buffer — only `Output` (always `Char*` for this MVP shape) gets
/// printed.
///
/// Arena lifecycle (the arena memory plan — see `arena.rs`'s module doc):
/// each `step` call allocates into whatever arena is current. Once it
/// returns, a fresh arena is swapped in and `State`'s new leaves are
/// deep-copied into it (the only allocations that need to survive into the
/// next iteration); the arena that just held the whole step's allocations —
/// `State`'s previous value, `Event`, `Output`, every intermediate value —
/// is then dropped, freeing everything not copied.
///
/// # Safety
/// `seed`/`step` must be the genuine trampolines for a `State` of exactly
/// `n_state_leaves` i64 leaves — an `unsafe extern "C" fn` pointer carries
/// no leaf-count information the compiler can check for you. `state_shape`
/// must describe that same `State` Kind — a mismatch (e.g. the wrong leaf
/// count or backing) means `deep_copy_leaves` reads or writes leaves
/// incorrectly.
pub unsafe fn drive_event_loop(
    seed: unsafe extern "C" fn(*mut i64),
    step: unsafe extern "C" fn(*mut i64, *mut i64),
    n_state_leaves: usize,
    state_shape: LeafShape,
) {
    // Native `cantor run`/`cantor build` only ever compile a `CharStar`
    // Output program (`codegen::aot::build_executable`'s guard) — there is
    // no terminal renderer for `Image`, so this is not a "for now"
    // shortcut, it's the permanent scope of this stdin/stdout driver.
    let mut loop_state = unsafe {
        EventLoop::new(
            seed,
            step,
            OutputKind::CharStar,
            n_state_leaves,
            state_shape,
        )
    };

    let stdin = std::io::stdin();
    let mut lines = stdin.lock().lines();

    loop {
        let (event, is_final) = match lines.next() {
            Some(Ok(line)) => (line, false),
            Some(Err(e)) => {
                eprintln!("error reading stdin: {e}");
                std::process::exit(1);
            }
            None => (EOT_EVENT.to_string(), true),
        };

        let OutputValue::CharStar(output) = loop_state.step(&event) else {
            unreachable!("drive_event_loop always constructs OutputKind::CharStar");
        };
        println!("{output}");

        if is_final {
            break;
        }
    }
}

/// One suspended event-loop program: the compiled `step` trampoline plus the
/// `State` carried between calls. Driving it one `Event` at a time — rather
/// than owning a read loop the way `drive_event_loop` does — is what lets a
/// host that *can't* block on stdin run the same program: the browser shim
/// (see `cantor build --target wasm32`) calls `step` from a JS event handler
/// and returns to the JS event loop in between.
pub struct EventLoop {
    step: unsafe extern "C" fn(*mut i64, *mut i64),
    output_kind: OutputKind,
    /// `State`'s Kind leaves, live across calls. Its length is the
    /// `n_state_leaves` given to `new`.
    state_buf: Vec<i64>,
    state_shape: LeafShape,
}

impl EventLoop {
    /// Seed `State` by calling the program's 0-arity `main` trampoline.
    ///
    /// # Safety
    /// Same contract as [`drive_event_loop`]: `seed`/`step` must be the
    /// genuine trampolines for a `State` of exactly `n_state_leaves` i64
    /// leaves, and `state_shape` must describe that same `State` Kind.
    /// `output_kind` must match `step`'s actual compiled Output Kind — a
    /// mismatch means `decode_output` reads the wrong number of leaves as
    /// State's own, corrupting everything after.
    pub unsafe fn new(
        seed: unsafe extern "C" fn(*mut i64),
        step: unsafe extern "C" fn(*mut i64, *mut i64),
        output_kind: OutputKind,
        n_state_leaves: usize,
        state_shape: LeafShape,
    ) -> Self {
        let mut state_buf = vec![0i64; n_state_leaves];
        unsafe {
            seed(state_buf.as_mut_ptr());
        }
        Self {
            step,
            output_kind,
            state_buf,
            state_shape,
        }
    }

    /// Feed one `Event` through the program and return its decoded `Output`.
    pub fn step(&mut self, event: &str) -> OutputValue {
        let n_state_leaves = self.state_buf.len();
        let n_output_leaves = self.output_kind.leaf_count();

        let mut in_buf = Vec::with_capacity(1 + n_state_leaves);
        in_buf.push(encode_char_star(event));
        in_buf.extend_from_slice(&self.state_buf);

        let mut out_buf = vec![0i64; n_output_leaves + n_state_leaves];
        unsafe {
            (self.step)(in_buf.as_mut_ptr(), out_buf.as_mut_ptr());
        }

        // Decode `Output` into owned Rust memory before the arena swap
        // below — it was allocated by this step, so it dies with `old`.
        let output = decode_output(self.output_kind, &out_buf[..n_output_leaves]);

        // Everything this step allocated (including the Output just read and
        // the previous State) lives in `old` from here on — deep-copy the new
        // State's leaves into the now-current fresh arena first, then drop
        // `old` to actually reclaim the rest.
        let old_arena = arena::swap(arena::Arena::new());
        let new_state = deep_copy::deep_copy_leaves(&self.state_shape, &out_buf[n_output_leaves..]);
        self.state_buf.copy_from_slice(&new_state);
        drop(old_arena);

        output
    }
}
