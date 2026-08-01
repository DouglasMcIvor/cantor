//! `write_object_file`/`compile_to_object` — the AOT backend's object-file
//! emission, ahead of the full `cantor build` link pipeline (tests/cli).

use cantor::codegen::{BuildTarget, compile_to_object};
use cantor::parser::parse_file;
use inkwell::context::Context;

/// Compile a trivial program for `target` and return the emitted object
/// file's bytes.
fn object_bytes(target: BuildTarget, tag: &str) -> Vec<u8> {
    let src = "main : Nat -> Nat\nmain(x) = x + 1\n";
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
