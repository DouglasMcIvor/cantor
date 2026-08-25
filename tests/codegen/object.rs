//! `write_object_file`/`compile_to_object` — the AOT backend's object-file
//! emission, ahead of the full `cantor build` link pipeline (tests/cli).

use cantor::codegen::{BuildTarget, compile_to_object};
use cantor::parser::parse_file;
use inkwell::context::Context;

/// Compile a trivial program for `target` and return the emitted object
/// file's bytes.
fn object_bytes(target: BuildTarget, tag: &str) -> Vec<u8> {
    object_bytes_of("main : Nat -> Nat\nmain(x) = x + 1\n", target, tag)
}

/// As [`object_bytes`], but for a caller-supplied program.
fn object_bytes_of(src: &str, target: BuildTarget, tag: &str) -> Vec<u8> {
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();

    let dir = std::env::temp_dir().join(format!("cantor-object-test-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("out.o");

    compile_to_object(&ctx, &items, &path, target).unwrap_or_else(|e| panic!("compile error: {e}"));

    let bytes = std::fs::read(&path).expect("object file should have been written");
    std::fs::remove_dir_all(&dir).ok();
    bytes
}

#[test]
fn compiles_to_a_non_empty_elf_object() {
    let bytes = object_bytes(BuildTarget::Native, "native");
    assert!(!bytes.is_empty(), "object file should be non-empty");
    // ELF magic — the native target only runs on Linux CI/dev machines today.
    assert_eq!(&bytes[0..4], b"\x7fELF", "expected an ELF object file");
}

#[test]
fn compiles_to_a_wasm_object() {
    let bytes = object_bytes(BuildTarget::Wasm32, "wasm");
    assert!(!bytes.is_empty(), "object file should be non-empty");
    // WebAssembly object magic: a NUL byte followed by "asm".
    assert_eq!(&bytes[0..4], b"\0asm", "expected a wasm object file");
}

/// The uniform call ABI widens every scalar return to i64, so a call into a
/// function whose declared range is `Unsigned32`/`Signed32`/`Char` has to be
/// truncated back to that Kind's i32 wire type at the call site. Without
/// that, the value keeps claiming the narrow Kind while actually being an
/// i64, and building a sequence literal out of it emits
/// `insertvalue { i32 } undef, i64 …` — invalid IR.
///
/// This only ever surfaced here rather than under `cantor run`, because
/// object emission runs the LLVM module verifier and the JIT does not.
#[test]
fn narrow_scalar_return_is_truncated_at_the_call_site() {
    let src = "\
mk : Nat -> Unsigned32
mk(v) = unsigned32(255)

main : Nat -> Unsigned32*
main(x) = [mk(x)]
";
    let bytes = object_bytes_of(src, BuildTarget::Native, "narrow-ret");
    assert!(!bytes.is_empty(), "object file should be non-empty");
    assert_eq!(&bytes[0..4], b"\x7fELF", "expected an ELF object file");
}
