use std::process;

use inkwell::context::Context;

use std::collections::HashMap;

use cantor::{
    ast::Item,
    codegen::compile_file,
    kind::{Kind, range_kind},
    names::check_names,
    parser::parse_file,
    solver::{CheckResult, check_file},
};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let (do_run, path) = match args.len() {
        2 if args[1] != "run" => (false, args[1].as_str()),
        3 if args[1] == "run" => (true, args[2].as_str()),
        _ => {
            eprintln!("usage: cantor <file.cantor>");
            eprintln!("       cantor run <file.cantor>");
            process::exit(2);
        }
    };

    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read `{path}`: {e}");
            process::exit(1);
        }
    };

    let items = match parse_file(&src) {
        Ok(items) => items,
        Err(e) => {
            match e.location(&src) {
                Some((line, col)) => eprintln!("{path}:{line}:{col}: {e}"),
                None              => eprintln!("{path}: {e}"),
            }
            process::exit(1);
        }
    };

    if items.is_empty() {
        println!("{path}: no definitions found");
        return;
    }

    let naming_errors = check_names(&items);
    if !naming_errors.is_empty() {
        for e in &naming_errors {
            match e.location(&src) {
                Some((line, col)) => eprintln!("{path}:{line}:{col}: {e}"),
                None              => eprintln!("{path}: {e}"),
            }
        }
        process::exit(1);
    }

    let all_results = match check_file(&items) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("internal error: {e}");
            process::exit(1);
        }
    };

    let mut n_proved = 0usize;
    let mut n_counter = 0usize;
    let mut n_unknown = 0usize;

    // Build a name → item map so we can look up the full signature display for
    // each result without relying on positional alignment (unannotated NameDefs
    // produce no check result, so zipping items with all_results is unsafe).
    let item_by_name: HashMap<&str, &Item> = items
        .iter()
        .filter_map(|item| match item {
            Item::FunctionDef(def) => Some((def.name.0.as_str(), item)),
            Item::NameDef(def) => Some((def.name.0.as_str(), item)),
        })
        .collect();

    for (name, sig_results) in &all_results {
        let item = item_by_name.get(name.as_str());
        for (i, (label, result)) in sig_results.iter().enumerate() {
            let sig_display = match item {
                Some(Item::FunctionDef(def)) => format!("{} : {}", def.name, def.sigs[i]),
                Some(Item::NameDef(_)) | None => label.clone(),
            };

            match result {
                CheckResult::Proved => {
                    println!("  proved          {sig_display}");
                    n_proved += 1;
                }
                CheckResult::Counterexample { params, output, reason } => {
                    println!("  counterexample  {sig_display}");
                    let mut pairs: Vec<_> = params.iter().collect();
                    pairs.sort_by_key(|(k, _)| k.as_str());
                    let bindings = pairs
                        .iter()
                        .map(|(k, v)| format!("{k} = {v}"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!("    {bindings}  ->  output = {output}  ({reason})");
                    n_counter += 1;
                }
                CheckResult::Unknown(reason) => {
                    println!("  unknown         {sig_display}");
                    println!("    ({reason})");
                    n_unknown += 1;
                }
            }
        }
    }

    println!();
    println!(
        "  {} proved, {} counterexample(s), {} unknown",
        n_proved, n_counter, n_unknown
    );

    if do_run {
        run_main(&items, n_counter, n_unknown, path);
    } else if n_counter > 0 || n_unknown > 0 {
        process::exit(1);
    }
}

fn run_main(items: &[Item], n_counter: usize, n_unknown: usize, path: &str) {
    let has_main = items.iter().any(|item| match item {
        Item::FunctionDef(def) => def.name.0 == "main" && def.params.is_empty(),
        Item::NameDef(_) => false,
    });

    if !has_main {
        eprintln!("error: `cantor run` requires a zero-argument `main` function");
        process::exit(1);
    }

    if n_counter > 0 {
        eprintln!(
            "error: not running — {} counterexample(s) found above",
            n_counter
        );
        process::exit(1);
    }

    if n_unknown > 0 {
        eprintln!(
            "warning: {} signature(s) could not be fully verified — running anyway",
            n_unknown
        );
    }

    let ctx = Context::create();
    let engine = match compile_file(&ctx, items) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("{path}: compile error: {e}");
            process::exit(1);
        }
    };

    // Determine main's return Kind from the first signature.
    let main_return_kind = items.iter().find_map(|item| match item {
        Item::FunctionDef(def) if def.name.0 == "main" && def.params.is_empty() => {
            def.sigs.first().map(|s| range_kind(&s.range))
        }
        _ => None,
    }).unwrap_or(Kind::Int);

    match &main_return_kind {
        // Fallible main: the runner converts {i1, i64} → flat i64 (sentinel on failure).
        Kind::Tuple(elems) if elems.first() == Some(&Kind::Fail) => {
            let _ = elems; // used in the match guard only
            let result = unsafe {
                let f = engine
                    .get_function::<unsafe extern "C" fn() -> i64>("__cantor_main_runner")
                    .unwrap_or_else(|e| {
                        eprintln!("internal error: could not find `__cantor_main_runner`: {e}");
                        process::exit(1);
                    });
                f.call()
            };
            if result == i64::MIN {
                // Read the typed error code stored by the runner via the JIT getter.
                let error_code: i64 = unsafe {
                    match engine.get_function::<unsafe extern "C" fn() -> i64>(
                        "__cantor_get_fail_code",
                    ) {
                        Ok(f) => f.call(),
                        Err(_) => 0,
                    }
                };
                if error_code != 0 {
                    eprintln!("\nmain() failed with error code {error_code}");
                } else {
                    eprintln!("\nmain() failed: assertion failed at runtime");
                }
                process::exit(1);
            } else {
                println!("\nmain() = {result}");
            }
        }
        // Tuple-returning main: use the buffer trampoline.
        Kind::Tuple(_) => {
            let n_leaves = count_kind_leaves(&main_return_kind);
            let mut buf = vec![0i64; n_leaves];
            unsafe {
                let f = engine
                    .get_function::<unsafe extern "C" fn(*mut i64)>("cantor_main_into")
                    .unwrap_or_else(|e| {
                        eprintln!("internal error: could not find `cantor_main_into`: {e}");
                        process::exit(1);
                    });
                f.call(buf.as_mut_ptr());
            }
            let display = format_kind_val(&main_return_kind, &buf, &mut 0);
            println!("\nmain() = {display}");
        }
        // Non-fallible scalar main.
        _ => {
            let result = unsafe {
                let f = engine
                    .get_function::<unsafe extern "C" fn() -> i64>("main")
                    .unwrap_or_else(|e| {
                        eprintln!("internal error: could not find `main` in compiled module: {e}");
                        process::exit(1);
                    });
                f.call()
            };
            println!("\nmain() = {result}");
        }
    }
}

fn count_kind_leaves(kind: &Kind) -> usize {
    match kind {
        Kind::Int | Kind::Bool | Kind::Fail | Kind::Set(_) | Kind::Union(_) => 1,
        Kind::Tuple(elems) => elems.iter().map(count_kind_leaves).sum(),
        // TODO: tagged-union IR — count tag field + widest arm
        Kind::TaggedUnion(_) => 1,
        Kind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in CLI output"),
    }
}

fn format_kind_val(kind: &Kind, buf: &[i64], offset: &mut usize) -> String {
    match kind {
        Kind::Bool => { let v = buf[*offset] != 0; *offset += 1; format!("{v}") }
        Kind::Fail => { *offset += 1; "fail".to_string() }
        Kind::Int | Kind::Set(_) | Kind::Union(_) => { let v = buf[*offset]; *offset += 1; format!("{v}") }
        Kind::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(|k| format_kind_val(k, buf, offset)).collect();
            format!("({})", parts.join(", "))
        }
        // TODO: tagged-union IR — decode tag and display the active arm
        Kind::TaggedUnion(_) => { let v = buf[*offset]; *offset += 1; format!("<tagged-union {v}>") }
        Kind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in CLI output"),
    }
}
