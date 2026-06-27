use inkwell::context::Context;
use rustyline::{DefaultEditor, error::ReadlineError};

use cantor::{
    ast::{FunctionBody, FunctionDef, Item},
    codegen::compile_file,
    error::CompileError,
    names::check_names,
    parser::{parse_expr, parse_file},
    solver::{CheckResult, check_file},
    span::{Span, Symbol},
};

const PROMPT: &str = "ℵ> ";
const CONT_PROMPT: &str = "   ";

struct ReplState {
    items: Vec<Item>,
}

pub fn run() {
    println!("Cantor REPL  —  :help for commands, Ctrl-D to exit");
    println!();

    let mut state = ReplState { items: vec![] };
    let mut rl = DefaultEditor::new().unwrap_or_else(|e| {
        eprintln!("error: could not initialise line editor: {e}");
        std::process::exit(1);
    });

    loop {
        match read_complete_input(&mut rl) {
            Ok(input) => {
                let trimmed = input.trim();
                if trimmed.is_empty() {
                    continue;
                }
                if let Some(cmd) = trimmed.strip_prefix(':') {
                    if !handle_command(&mut state, cmd.trim()) {
                        break;
                    }
                } else {
                    process_input(&mut state, &input);
                }
            }
            Err(ReadlineError::Interrupted) => {
                eprintln!("(interrupted — use :quit or Ctrl-D to exit)");
            }
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("error: {e}");
                break;
            }
        }
    }

    println!("Goodbye.");
}

fn read_complete_input(rl: &mut DefaultEditor) -> Result<String, ReadlineError> {
    let mut input = String::new();
    loop {
        let prompt = if input.is_empty() { PROMPT } else { CONT_PROMPT };
        let line = rl.readline(prompt)?;
        if !input.is_empty() {
            input.push('\n');
        }
        input.push_str(&line);

        if !needs_more_input(&input) {
            if !input.trim().is_empty() {
                rl.add_history_entry(input.as_str()).ok();
            }
            return Ok(input);
        }
    }
}

fn is_eof_error(e: &CompileError) -> bool {
    matches!(e, CompileError::UnexpectedToken { found, .. } if found == "<eof>")
}

fn needs_more_input(input: &str) -> bool {
    if input.trim().is_empty() {
        return false;
    }
    match parse_file(input) {
        Ok(_) => return false,
        Err(e) if is_eof_error(&e) => return true,
        Err(_) => {}
    }
    matches!(parse_expr(input), Err(e) if is_eof_error(&e))
}

fn handle_command(state: &mut ReplState, cmd: &str) -> bool {
    match cmd {
        "q" | "quit" => return false,
        "h" | "help" => {
            println!("Commands:");
            println!("  :help  :h    show this help");
            println!("  :defs        list all active definitions");
            println!("  :reset       clear all definitions");
            println!("  :quit  :q    exit the REPL");
            println!();
            println!("Enter a function or name definition to add it to the environment.");
            println!("Enter an expression to evaluate it.");
            println!();
            println!("Note: bare expression evaluation supports Int-returning expressions.");
            println!("For functions with non-Int results, define them with a signature.");
        }
        "defs" => {
            if state.items.is_empty() {
                println!("  (no definitions)");
            } else {
                for item in &state.items {
                    match item {
                        Item::FunctionDef(def) => {
                            if def.sigs.is_empty() {
                                println!("  {}", def.name);
                            } else {
                                for sig in &def.sigs {
                                    println!("  {} : {}", def.name, sig);
                                }
                            }
                        }
                        Item::NameDef(def) => println!("  {}", def.name),
                    }
                }
            }
        }
        "reset" => {
            state.items.clear();
            println!("  (definitions cleared)");
        }
        other => {
            eprintln!("  unknown command :{other}  (try :help)");
        }
    }
    true
}

fn process_input(state: &mut ReplState, input: &str) {
    match parse_file(input) {
        Ok(new_items) if !new_items.is_empty() => {
            add_definitions(state, new_items, input);
            return;
        }
        Ok(_) => {}
        Err(ref e) if is_eof_error(e) => {
            // Shouldn't reach here — read_complete_input guards against it.
            eprintln!("  error: unexpected end of input");
            return;
        }
        Err(_) => {}
    }

    match parse_expr(input) {
        Ok(expr) => evaluate_expr(state, expr),
        Err(e) => print_error(&e, input),
    }
}

fn print_error(e: &CompileError, src: &str) {
    match e.location(src) {
        Some((line, col)) => eprintln!("  error at {line}:{col}: {e}"),
        None => eprintln!("  error: {e}"),
    }
}

fn add_definitions(state: &mut ReplState, new_items: Vec<Item>, src: &str) {
    let naming_errors = check_names(&new_items);
    if !naming_errors.is_empty() {
        for e in &naming_errors {
            print_error(e, src);
        }
        return;
    }

    // Merge: replace any existing definition with the same name.
    let mut redefined: Vec<String> = Vec::new();
    for new_item in &new_items {
        let name = item_name(new_item);
        if state.items.iter().any(|old| item_name(old) == name) {
            redefined.push(name.to_owned());
            state.items.retain(|old| item_name(old) != name);
        }
    }
    if !redefined.is_empty() {
        println!("  (redefined {})", redefined.join(", "));
    }
    state.items.extend(new_items.clone());

    match check_file(&state.items) {
        Ok(results) => {
            let mut any_result = false;
            for new_item in &new_items {
                let name = item_name(new_item);
                if let Some((_, sig_results)) = results.iter().find(|(n, _)| n == name) {
                    for (i, (_, result)) in sig_results.iter().enumerate() {
                        let label = match new_item {
                            Item::FunctionDef(def) if i < def.sigs.len() => {
                                format!("{} : {}", def.name, def.sigs[i])
                            }
                            _ => name.to_owned(),
                        };
                        display_check_result(&label, result);
                        any_result = true;
                    }
                }
            }
            if !any_result {
                let names: Vec<_> = new_items.iter().map(item_name).collect();
                println!("  defined         {}", names.join(", "));
            }
        }
        Err(e) => {
            eprintln!("  solver error: {e}");
            // Roll back additions that couldn't be verified.
            for new_item in &new_items {
                let name = item_name(new_item);
                state.items.retain(|i| item_name(i) != name);
            }
        }
    }
}

fn display_check_result(label: &str, result: &CheckResult) {
    match result {
        CheckResult::Proved => {
            println!("  proved          {label}");
        }
        CheckResult::Counterexample { params, output, reason } => {
            println!("  counterexample  {label}");
            let mut pairs: Vec<_> = params.iter().collect();
            pairs.sort_by_key(|(k, _)| k.as_str());
            let bindings = pairs
                .iter()
                .map(|(k, v)| format!("{k} = {v}"))
                .collect::<Vec<_>>()
                .join(", ");
            println!("    {bindings}  ->  output = {output}  ({reason})");
        }
        CheckResult::Unknown(reason) => {
            println!("  unknown         {label}");
            println!("    ({reason})");
        }
    }
}

fn evaluate_expr(state: &ReplState, expr: cantor::ast::Expr) {
    // Synthesise `main() = <expr>` with no signature; codegen defaults to Kind::Int.
    // TODO: infer the result Kind from the expression so Bool/Tuple results display correctly.
    // For now, tuple-returning expressions will fail at LLVM verification (caught by into_jit_engine).
    let synthetic = Item::FunctionDef(FunctionDef {
        name: Symbol::new("main"),
        sigs: vec![],
        params: vec![],
        body: FunctionBody::Expr(expr),
        span: Span::dummy(),
    });

    let mut all_items = state.items.clone();
    all_items.push(synthetic);

    let ctx = Context::create();
    let engine = match compile_file(&ctx, &all_items) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("  error: {e}");
            return;
        }
    };

    let result = unsafe {
        match engine.get_function::<unsafe extern "C" fn() -> i64>("main") {
            Ok(f) => f.call(),
            Err(e) => {
                eprintln!("  error: could not call compiled expression: {e}");
                return;
            }
        }
    };
    println!("  {result}");
}

fn item_name(item: &Item) -> &str {
    match item {
        Item::FunctionDef(def) => def.name.0.as_str(),
        Item::NameDef(def) => def.name.0.as_str(),
    }
}
