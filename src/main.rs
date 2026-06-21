use std::process;

use inkwell::context::Context;

use cantor::{
    ast::Item,
    codegen::{FAIL_SENTINEL, compile_file},
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

    for (item, (_name, sig_results)) in items.iter().zip(all_results.iter()) {
        for (i, (label, result)) in sig_results.iter().enumerate() {
            let sig_display = match item {
                Item::FunctionDef(def) => format!("{} : {}", def.name, def.sigs[i]),
                Item::NameDef(_) => label.clone(),
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

    let result = unsafe {
        let f = engine
            .get_function::<unsafe extern "C" fn() -> i64>("main")
            .unwrap_or_else(|e| {
                eprintln!("internal error: could not find `main` in compiled module: {e}");
                process::exit(1);
            });
        f.call()
    };

    if result == FAIL_SENTINEL {
        eprintln!("\nmain() failed: assertion failed at runtime");
        process::exit(1);
    } else {
        println!("\nmain() = {result}");
    }
}
