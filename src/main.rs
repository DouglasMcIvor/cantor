mod repl;

use std::process;

use inkwell::context::Context;

use std::collections::HashMap;

use cantor::{
    ast::Item,
    codegen::{compile_constrained, compile_to_ir},
    kind::Kind,
    names::check_names,
    parser::parse_file,
    semantics::tree::SemItem,
    solver::{CheckOutcome, CheckResult, ConstrainedTree, check_file},
};

const DEFAULT_TIMEOUT_SECS: u64 = 60;
pub(crate) const DEFAULT_TIMEOUT_MS: u64 = DEFAULT_TIMEOUT_SECS * 1000;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Strip out --timeout <n> / --timeout=<n> before positional parsing.
    let mut timeout_secs: u64 = DEFAULT_TIMEOUT_SECS;
    let mut positional: Vec<&str> = Vec::new();
    let mut i = 1;
    while i < args.len() {
        if args[i] == "--timeout" {
            i += 1;
            if i >= args.len() {
                eprintln!("error: --timeout requires a value in seconds");
                process::exit(2);
            }
            timeout_secs = match args[i].parse() {
                Ok(n) => n,
                Err(_) => {
                    eprintln!("error: --timeout value must be a non-negative integer (seconds)");
                    process::exit(2);
                }
            };
        } else if let Some(val) = args[i].strip_prefix("--timeout=") {
            timeout_secs = match val.parse() {
                Ok(n) => n,
                Err(_) => {
                    eprintln!("error: --timeout value must be a non-negative integer (seconds)");
                    process::exit(2);
                }
            };
        } else {
            positional.push(args[i].as_str());
        }
        i += 1;
    }
    let timeout_ms = timeout_secs * 1000;

    let (do_run, do_llvm_ir, path) = match positional.len() {
        0 => {
            repl::run();
            return;
        }
        1 if positional[0] != "run" && positional[0] != "llvm-ir" => {
            (false, false, positional[0])
        }
        2 if positional[0] == "run" => (true, false, positional[1]),
        2 if positional[0] == "llvm-ir" => (false, true, positional[1]),
        _ => {
            eprintln!("usage: cantor [--timeout <secs>]");
            eprintln!("       cantor [--timeout <secs>] <file.cantor>");
            eprintln!("       cantor [--timeout <secs>] run <file.cantor>");
            eprintln!("       cantor llvm-ir <file.cantor>");
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

    // `llvm-ir` is a pure codegen debugging tool: skip the SMT solver
    // entirely and go straight to LLVM IR, printed to stdout.
    if do_llvm_ir {
        let ctx = Context::create();
        match compile_to_ir(&ctx, &items) {
            Ok(ir) => {
                println!("{ir}");
                return;
            }
            Err(e) => {
                eprintln!("{path}: compile error: {e}");
                process::exit(1);
            }
        }
    }

    let outcome = match check_file(&items, timeout_ms) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("internal error: {e}");
            process::exit(1);
        }
    };

    // Display works identically whether or not the file was fully proved —
    // only `do_run` below cares about which `CheckOutcome` arm this is.
    let all_results: &[(String, Vec<(String, CheckResult)>)] = match &outcome {
        CheckOutcome::Proved(tree) => &tree.results,
        CheckOutcome::NotProved(results) => results,
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

    for (name, sig_results) in all_results {
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
        match outcome {
            CheckOutcome::Proved(tree) => run_main(tree, path),
            CheckOutcome::NotProved(_) => {
                eprintln!(
                    "error: not running — {} counterexample(s), {} unknown result(s) found above",
                    n_counter, n_unknown
                );
                process::exit(1);
            }
        }
    } else if n_counter > 0 || n_unknown > 0 {
        process::exit(1);
    }
}

fn run_main(tree: ConstrainedTree, path: &str) {
    let has_main = tree.items.iter().any(|item| match item {
        Item::FunctionDef(def) => def.name.0 == "main" && def.params.is_empty(),
        Item::NameDef(_) => false,
    });

    if !has_main {
        eprintln!("error: `cantor run` requires a zero-argument `main` function");
        process::exit(1);
    }

    let ctx = Context::create();
    let engine = match compile_constrained(&ctx, &tree) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("{path}: compile error: {e}");
            process::exit(1);
        }
    };

    // Determine main's return Kind from the already-elaborated tree — no need
    // to recompute it from the raw ast via `wire::range_kind` a second time.
    let main_return_kind = tree.sem_items.iter().find_map(|item| match item {
        SemItem::FunctionDef(def) if def.name.0 == "main" && def.params.is_empty() => {
            Some(def.return_kind.clone())
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
        Kind::Int | Kind::Bool | Kind::Fail | Kind::Set(_) => 1,
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
        Kind::Int | Kind::Set(_) => { let v = buf[*offset]; *offset += 1; format!("{v}") }
        Kind::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(|k| format_kind_val(k, buf, offset)).collect();
            format!("({})", parts.join(", "))
        }
        // TODO: tagged-union IR — decode tag and display the active arm
        Kind::TaggedUnion(_) => { let v = buf[*offset]; *offset += 1; format!("<tagged-union {v}>") }
        Kind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in CLI output"),
    }
}
