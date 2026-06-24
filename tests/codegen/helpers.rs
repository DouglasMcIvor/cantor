use cantor::{
    ast::{Expr, Param},
    codegen::{compile_file, compile_to_ir, Compiler},
};
use inkwell::context::Context;

pub fn jit_eval(body: Expr) -> i64 {
    jit_eval_fn(&[], body, &[])
}

pub fn jit_eval_fn(params: &[Param], body: Expr, args: &[i64]) -> i64 {
    let ctx = Context::create();
    let mut compiler = Compiler::new(&ctx, "test");
    compiler.compile_function("__test__", params, &body).unwrap();
    let engine = compiler.into_jit_engine().unwrap();
    unsafe {
        match args.len() {
            0 => {
                let f = engine
                    .get_function::<unsafe extern "C" fn() -> i64>("__test__")
                    .unwrap();
                f.call()
            }
            1 => {
                let f = engine
                    .get_function::<unsafe extern "C" fn(i64) -> i64>("__test__")
                    .unwrap();
                f.call(args[0])
            }
            2 => {
                let f = engine
                    .get_function::<unsafe extern "C" fn(i64, i64) -> i64>("__test__")
                    .unwrap();
                f.call(args[0], args[1])
            }
            _ => panic!("jit_eval_fn: add more arms for >{} params", args.len()),
        }
    }
}

pub fn jit_src_one_arg(src: &str, arg: i64) -> i64 {
    use cantor::parser::parse_file;
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let engine = compile_file(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"));
    unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn(i64) -> i64>("main")
            .unwrap();
        f.call(arg)
    }
}

pub fn jit_src_zero_arg(src: &str) -> i64 {
    use cantor::parser::parse_file;
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let engine = compile_file(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"));
    unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn() -> i64>("main")
            .unwrap();
        f.call()
    }
}

/// Compile a zero-arg fallible `main` (range `X | Fail` or `X !! Y`) and run it.
///
/// Returns `Ok(payload)` on success or `Err(error_code)` on failure.
/// Uses `__cantor_main_runner` and `__cantor_get_fail_code` emitted by the compiler.
pub fn jit_src_zero_arg_fallible(src: &str) -> Result<i64, i64> {
    use cantor::parser::parse_file;
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    let engine = compile_file(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"));
    unsafe {
        let runner = engine
            .get_function::<unsafe extern "C" fn() -> i64>("__cantor_main_runner")
            .unwrap_or_else(|e| panic!("could not find __cantor_main_runner: {e}"));
        let result = runner.call();
        if result == i64::MIN {
            let getter = engine
                .get_function::<unsafe extern "C" fn() -> i64>("__cantor_get_fail_code")
                .unwrap_or_else(|e| panic!("could not find __cantor_get_fail_code: {e}"));
            Err(getter.call())
        } else {
            Ok(result)
        }
    }
}

/// Compile `src` and return the LLVM IR as a string without running it.
///
/// Use this to assert whether a construct was handled at compile time
/// (no `cantor_set_*` calls in the IR) or emitted as runtime calls.
pub fn ir_for_src(src: &str) -> String {
    use cantor::parser::parse_file;
    let items = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    let ctx = Context::create();
    compile_to_ir(&ctx, &items).unwrap_or_else(|e| panic!("compile error: {e}"))
}
