use std::process;

use cantor::{
    ast::Item,
    parser::parse_file,
    solver::{CheckResult, check_file},
};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = match args.get(1) {
        Some(p) => p.as_str(),
        None => {
            eprintln!("usage: cantor <file.cantor>");
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

    // `check_file` preserves item order, so we can zip.
    for (item, (_fn_name, sig_results)) in items.iter().zip(all_results.iter()) {
        let Item::FunctionDef(def) = item;

        for (i, (_label, result)) in sig_results.iter().enumerate() {
            let sig = &def.sigs[i];
            let sig_display = format!("{} : {}", def.name, sig);

            match result {
                CheckResult::Proved => {
                    println!("  proved          {sig_display}");
                    n_proved += 1;
                }
                CheckResult::Counterexample { params, output } => {
                    println!("  counterexample  {sig_display}");
                    let mut pairs: Vec<_> = params.iter().collect();
                    pairs.sort_by_key(|(k, _)| k.as_str());
                    let bindings = pairs
                        .iter()
                        .map(|(k, v)| format!("{k} = {v}"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    println!("    {bindings}  ->  output = {output}  (not in {})", sig.range);
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

    if n_counter > 0 || n_unknown > 0 {
        process::exit(1);
    }
}
