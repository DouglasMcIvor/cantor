//! MVP IO event loop (docs/design-decisions.md §6) — shared by the JIT
//! (`cantor run`, main.rs) and AOT (`cantor build`, `src/codegen/aot.rs`)
//! backends. Only `drive_event_loop` differs between the two call sites:
//! JIT resolves `seed`/`step` via an `ExecutionEngine` lookup, AOT gets
//! them as ordinary statically-linked `extern "C"` function pointers — the
//! loop body itself, and every value encode/decode helper below, is
//! identical either way.

use std::io::BufRead;

use crate::{
    arena, cantor_vec_builder_finish_i64, cantor_vec_builder_new_i64, cantor_vec_builder_push_i64,
    cantor_vec_get_i64, cantor_vec_len_i64,
    deep_copy::{self, LeafShape},
};

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
    let mut loop_state = unsafe { EventLoop::new(seed, step, n_state_leaves, state_shape) };

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

        println!("{}", loop_state.step(&event));

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
    pub unsafe fn new(
        seed: unsafe extern "C" fn(*mut i64),
        step: unsafe extern "C" fn(*mut i64, *mut i64),
        n_state_leaves: usize,
        state_shape: LeafShape,
    ) -> Self {
        let mut state_buf = vec![0i64; n_state_leaves];
        unsafe {
            seed(state_buf.as_mut_ptr());
        }
        Self {
            step,
            state_buf,
            state_shape,
        }
    }

    /// Feed one `Event` through the program and return its `Output`.
    pub fn step(&mut self, event: &str) -> String {
        let n_state_leaves = self.state_buf.len();

        let mut in_buf = Vec::with_capacity(1 + n_state_leaves);
        in_buf.push(encode_char_star(event));
        in_buf.extend_from_slice(&self.state_buf);

        let mut out_buf = vec![0i64; 1 + n_state_leaves];
        unsafe {
            (self.step)(in_buf.as_mut_ptr(), out_buf.as_mut_ptr());
        }

        // Read `Output` out into an owned String before the arena swap
        // below — it was allocated by this step, so it dies with `old`.
        let output = format_char_vector(out_buf[0]);

        // Everything this step allocated (including the Output just read and
        // the previous State) lives in `old` from here on — deep-copy the new
        // State's leaves into the now-current fresh arena first, then drop
        // `old` to actually reclaim the rest.
        let old_arena = arena::swap(arena::Arena::new());
        let new_state = deep_copy::deep_copy_leaves(&self.state_shape, &out_buf[1..]);
        self.state_buf.copy_from_slice(&new_state);
        drop(old_arena);

        output
    }
}
