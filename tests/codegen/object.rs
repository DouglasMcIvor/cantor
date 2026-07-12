//! `write_object_file`/`compile_to_object` — the AOT backend's object-file
//! emission, ahead of the full `cantor build` link pipeline (tests/cli).

use cantor::codegen::compile_to_object;
use cantor::parser::parse_file;
use inkwell::context::Context;

#[test]
fn compiles_to_a_non_empty_elf_object() {
    let src = "main : Nat -> Nat\nmain(x) = x + 1\n";
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();

    let dir = std::env::temp_dir().join(format!("cantor-object-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("out.o");

    compile_to_object(&ctx, &items, &path).unwrap_or_else(|e| panic!("compile error: {e}"));

    let bytes = std::fs::read(&path).expect("object file should have been written");
    assert!(!bytes.is_empty(), "object file should be non-empty");
    // ELF magic — this test only runs on Linux CI/dev machines today (no
    // cross-target story yet, see write_object_file's doc comment).
    assert_eq!(&bytes[0..4], b"\x7fELF", "expected an ELF object file");

    std::fs::remove_dir_all(&dir).ok();
}
