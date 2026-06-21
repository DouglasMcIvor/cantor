use cantor::codegen::Compiler;
use inkwell::context::Context;

/// Verify that declaring runtime functions and then creating the JIT engine
/// correctly registers the symbols so the JIT can call them.
///
/// We build a trivial LLVM function that calls `cantor_set_new_i64()` and
/// returns the result. If the JIT cannot resolve the symbol it will crash or
/// return 0; a non-zero result means the linkage is working.
#[test]
fn cantor_set_new_i64_resolves_and_returns_pointer() {
    let ctx = Context::create();
    let mut compiler = Compiler::new(&ctx, "test");
    compiler.declare_runtime_functions();

    // Build: test_fn() -> i64 { return cantor_set_new_i64(); }
    // We use a block so the borrow of compiler (via module()) ends before
    // into_jit_engine() consumes it.
    let i64t = ctx.i64_type();
    let (wrapper_fn, new_i64_fn) = {
        let m = compiler.module();
        let wrapper = m.add_function("test_fn", i64t.fn_type(&[], false), None);
        let new_i64 = m.get_function("cantor_set_new_i64").unwrap();
        (wrapper, new_i64)
    };

    let entry = ctx.append_basic_block(wrapper_fn, "entry");
    let builder = ctx.create_builder();
    builder.position_at_end(entry);
    let ptr_val = builder
        .build_call(new_i64_fn, &[], "new_set")
        .unwrap()
        .try_as_basic_value()
        .left()
        .unwrap();
    builder.build_return(Some(&ptr_val)).unwrap();

    let ee = compiler.into_jit_engine().unwrap();
    let result = unsafe {
        let f = ee
            .get_function::<unsafe extern "C" fn() -> i64>("test_fn")
            .unwrap();
        f.call()
    };
    assert!(result != 0, "cantor_set_new_i64 should return a non-null pointer");
}
