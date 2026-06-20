use cantor::{
    ast::{Expr, Param},
    codegen::{compile_file, Compiler},
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
