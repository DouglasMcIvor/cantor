//! MVP IO event loop (docs/design-decisions.md §6) — shared by the JIT
//! (`cantor run`, main.rs) and AOT (`cantor build`, `src/codegen/aot.rs`)
//! backends. Only `drive_event_loop` differs between the two call sites:
//! JIT resolves `seed`/`step` via an `ExecutionEngine` lookup, AOT gets
//! them as ordinary statically-linked `extern "C"` function pointers — the
//! loop body itself, and every value encode/decode helper below, is
//! identical either way.

use std::io::BufRead;

use crate::{
    cantor_vec_builder_finish_i64, cantor_vec_builder_new_i64, cantor_vec_builder_push_i64,
    cantor_vec_get_i64, cantor_vec_len_i64,
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

/// The synthetic final `Event` fed to an event-loop `main` when `stdin`
/// closes: a length-1 `Char*` containing codepoint 4 (ASCII EOT, the
/// traditional Ctrl-D "end of transmission" control character — not
/// U+2404 ␄, which is a printable *display glyph* for EOT and could
/// theoretically appear in real input). docs/design-decisions.md §6.
pub fn encode_eot_event() -> i64 {
    encode_char_star("\u{4}")
}

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
/// already has (`count_kind_leaves(state_kind)`). `State` is never
/// formatted here — it's opaque, just copied between calls as a flat i64
/// buffer — only `Output` (always `Char*` for this MVP shape) gets printed.
///
/// # Safety
/// `seed`/`step` must be the genuine trampolines for a `State` of exactly
/// `n_state_leaves` i64 leaves — an `unsafe extern "C" fn` pointer carries
/// no leaf-count information the compiler can check for you.
pub unsafe fn drive_event_loop(
    seed: unsafe extern "C" fn(*mut i64),
    step: unsafe extern "C" fn(*mut i64, *mut i64),
    n_state_leaves: usize,
) {
    let mut state_buf = vec![0i64; n_state_leaves];
    unsafe {
        seed(state_buf.as_mut_ptr());
    }

    let stdin = std::io::stdin();
    let mut lines = stdin.lock().lines();

    loop {
        let (event_ptr, is_final) = match lines.next() {
            Some(Ok(line)) => (encode_char_star(&line), false),
            Some(Err(e)) => {
                eprintln!("error reading stdin: {e}");
                std::process::exit(1);
            }
            None => (encode_eot_event(), true),
        };

        let mut in_buf = Vec::with_capacity(1 + n_state_leaves);
        in_buf.push(event_ptr);
        in_buf.extend_from_slice(&state_buf);

        let mut out_buf = vec![0i64; 1 + n_state_leaves];
        unsafe {
            step(in_buf.as_mut_ptr(), out_buf.as_mut_ptr());
        }

        println!("{}", format_char_vector(out_buf[0]));
        state_buf.copy_from_slice(&out_buf[1..]);

        if is_final {
            break;
        }
    }
}
