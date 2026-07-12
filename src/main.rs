mod repl;

use std::io::BufRead;
use std::process;

use inkwell::context::Context;

use std::collections::HashMap;

use cantor::{
    ast::Item,
    codegen::{compile_constrained, compile_to_ir},
    error::CompileError,
    kind::Kind,
    pipeline::{FrontendError, parse_and_check_names, results_of},
    semantics::tree::SemItem,
    solver::{CheckOutcome, CheckResult, ConstrainedTree, check_file},
};

/// Single rendering path for every `CompileError` the CLI can hit, so ICEs
/// (no Cantor source span — `e.location` is `None`) and ordinary
/// diagnostics (undefined names, unsupported syntax, ...) are never
/// printed the same way. A diagnostic points at the user's file; an ICE
/// gets a "please report this" hint instead, since there's nothing in the
/// user's source for them to fix.
fn print_compile_error(path: &str, e: &CompileError, src: &str) {
    match e.location(src) {
        Some((line, col)) => eprintln!("{path}:{line}:{col}: {e}"),
        None => eprintln!("{path}: {e}"),
    }
    if e.is_ice() {
        eprintln!(
            "note: this is a bug in the Cantor compiler itself, not your program — please file an issue"
        );
    }
}

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
        1 if positional[0] != "run" && positional[0] != "llvm-ir" => (false, false, positional[0]),
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

    let items = match parse_and_check_names(&src) {
        Ok(items) => items,
        Err(FrontendError::Parse(e)) => {
            print_compile_error(path, &e, &src);
            process::exit(1);
        }
        Err(FrontendError::Naming(errors)) => {
            for e in &errors {
                print_compile_error(path, e, &src);
            }
            process::exit(1);
        }
    };

    if items.is_empty() {
        println!("{path}: no definitions found");
        return;
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
                print_compile_error(path, &e, &src);
                process::exit(1);
            }
        }
    }

    let outcome = match check_file(&items, timeout_ms) {
        Ok(o) => o,
        Err(e) => {
            print_compile_error(path, &e, &src);
            process::exit(1);
        }
    };

    // Display works identically whether or not the file was fully proved —
    // only `do_run` below cares about which `CheckOutcome` arm this is.
    let all_results = results_of(&outcome);

    let mut n_proved = 0usize;
    let mut n_counter = 0usize;
    let mut n_unknown = 0usize;

    // Build a name → items map so we can look up the full signature display
    // for each result without relying on a single positional zip against
    // `items` (unannotated NameDefs produce no check result at all, and
    // int-soundness-plan phase 2 means a name can have more than one
    // `FunctionDef`, plus synthetic disjointness-check entries with no
    // backing item of their own — see `next_item_idx` below).
    let mut items_by_name: HashMap<&str, Vec<&Item>> = HashMap::new();
    for item in &items {
        let name = match item {
            Item::FunctionDef(def) => def.name.0.as_str(),
            Item::NameDef(def) => def.name.0.as_str(),
            // No backing item of its own to look up — `validate_equiv_decls`
            // already keys its result under the `lhs` function's own name
            // (same synthetic-entry trick `check_overload_disjointness` uses).
            Item::EquivDecl { .. } => continue,
        };
        items_by_name.entry(name).or_default().push(item);
    }
    // `all_results` lists every function/name's check results in file order,
    // followed by the disjointness-check entries appended at the very end
    // (see `check_overload_disjointness`) — so consuming one item per
    // same-named entry, in order, correctly pairs each genuine entry with
    // its `FunctionDef`/`NameDef` and leaves the trailing disjointness
    // entries (whose name's items are already exhausted) with `None`.
    let mut next_item_idx: HashMap<&str, usize> = HashMap::new();

    for (name, sig_results) in all_results {
        let idx = next_item_idx.entry(name.as_str()).or_insert(0);
        let item = items_by_name.get(name.as_str()).and_then(|v| v.get(*idx));
        *idx += 1;
        for (i, (label, result)) in sig_results.iter().enumerate() {
            let sig_display = match item {
                Some(Item::FunctionDef(def)) => match def.sigs.get(i) {
                    Some(sig) => format!("{} : {}", def.name, sig),
                    None => label.clone(),
                },
                Some(Item::NameDef(_)) | Some(Item::EquivDecl { .. }) | None => label.clone(),
            };

            match result {
                CheckResult::Proved => {
                    println!("  proved          {sig_display}");
                    n_proved += 1;
                }
                CheckResult::Counterexample {
                    params,
                    output,
                    reason,
                } => {
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
            CheckOutcome::Proved(tree) => run_main(tree, path, &src),
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

fn run_main(tree: ConstrainedTree, path: &str, src: &str) {
    // MVP IO event loop (docs/design-decisions.md §6): a 2-arity `main`
    // shaped like `Char* * S -> Char* * S` takes over `cantor run` entirely
    // — dispatch to the event-loop driver instead of the zero-arg path
    // below. Shape/identifier validity was already fully verified by
    // `solver::event_loop::validate_event_loop_main` before this
    // `ConstrainedTree` could exist, so this is a Kind-only re-scan.
    if let Some(state_kind) = find_event_loop_state_kind(&tree) {
        run_event_loop(tree, path, src, state_kind);
        return;
    }

    let has_main = tree.items.iter().any(|item| match item {
        Item::FunctionDef(def) => def.name.0 == "main" && def.params.is_empty(),
        Item::NameDef(_) | Item::EquivDecl { .. } => false,
    });

    if !has_main {
        eprintln!("error: `cantor run` requires a zero-argument `main` function");
        process::exit(1);
    }

    let ctx = Context::create();
    let engine = match compile_constrained(&ctx, &tree, path, src) {
        Ok(e) => e,
        Err(e) => {
            print_compile_error(path, &e, src);
            process::exit(1);
        }
    };

    // Determine main's return Kind from the already-elaborated tree — no need
    // to recompute it from the raw ast via `wire::range_kind` a second time.
    let main_return_kind = tree
        .sem_items
        .iter()
        .find_map(|item| match item {
            SemItem::FunctionDef(def) if def.name.0 == "main" && def.params.is_empty() => {
                Some(def.return_kind.clone())
            }
            _ => None,
        })
        .unwrap_or(Kind::Int);

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
                    match engine
                        .get_function::<unsafe extern "C" fn() -> i64>("__cantor_get_fail_code")
                    {
                        Ok(f) => f.call(),
                        Err(_) => 0,
                    }
                };
                if error_code != 0 {
                    // int-soundness-plan phase 3 step 4b: the error code is
                    // the Fail-wire's `Kind::Int` payload — tagged.
                    eprintln!(
                        "\nmain() failed with error code {}",
                        format_tagged_int(error_code)
                    );
                } else {
                    eprintln!("\nmain() failed: assertion failed at runtime");
                }
                process::exit(1);
            } else {
                // int-soundness-plan phase 3 step 4b: the success payload
                // (elems[1]) is `Kind::Int` (tagged) for an ordinary
                // fallible function — decode before printing.
                let display = if elems.get(1) == Some(&Kind::Int) {
                    format_tagged_int(result)
                } else {
                    result.to_string()
                };
                println!("\nmain() = {display}");
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
            // int-soundness-plan phase 3 step 4b: `Kind::Int` is tagged,
            // everything else (`Bool`, `Int64`, `Set`, …) is a plain i64.
            let display = if main_return_kind == Kind::Int {
                format_tagged_int(result)
            } else if main_return_kind == Kind::Char {
                format_char(result)
            } else if main_return_kind == Kind::Vector(Box::new(Kind::Char)) {
                format_char_vector(result)
            } else {
                result.to_string()
            };
            println!("\nmain() = {display}");
        }
    }
}

/// MVP IO event loop (docs/design-decisions.md §6) detection: find the
/// State `Kind` of a 2-arity `main` shaped like `Char* * S -> Char* * S`, if
/// the file defines one. `None` means this file just isn't using the
/// event-loop feature (an ordinary zero-arg `main`, or none at all).
fn find_event_loop_state_kind(tree: &ConstrainedTree) -> Option<Kind> {
    tree.sem_items.iter().find_map(|item| match item {
        SemItem::FunctionDef(def)
            if def.name.0 == "main"
                && is_event_loop_step_shape(&def.param_kinds, &def.return_kind) =>
        {
            let Kind::Tuple(elems) = &def.return_kind else {
                unreachable!("is_event_loop_step_shape already checked this is a Tuple");
            };
            Some(elems[1].clone())
        }
        _ => None,
    })
}

/// True when `(param_kinds, return_kind)` matches the MVP event loop's fixed
/// v0 shape `Char* * S -> Char* * S`. Duplicates `codegen`'s private
/// predicate of the same name (a few lines) rather than exposing it across
/// the lib/bin crate boundary just for this.
fn is_event_loop_step_shape(param_kinds: &[Kind], return_kind: &Kind) -> bool {
    let is_char_star = |k: &Kind| matches!(k, Kind::Vector(elem) if **elem == Kind::Char);
    param_kinds.len() == 2
        && is_char_star(&param_kinds[0])
        && matches!(return_kind, Kind::Tuple(elems) if elems.len() == 2 && is_char_star(&elems[0]))
}

/// MVP IO event loop driver (docs/design-decisions.md §6): compiles the
/// event-loop `main` and drives it against `stdin`, one line per `Event`,
/// until `stdin` closes — at which point it feeds one final synthetic
/// `Event` (a length-1 `Char*` containing codepoint 4, ASCII EOT) and
/// terminates unconditionally, regardless of the `State` that final call
/// returns.
fn run_event_loop(tree: ConstrainedTree, path: &str, src: &str, state_kind: Kind) {
    let ctx = Context::create();
    let engine = match compile_constrained(&ctx, &tree, path, src) {
        Ok(e) => e,
        Err(e) => {
            print_compile_error(path, &e, src);
            process::exit(1);
        }
    };

    let n_state_leaves = count_kind_leaves(&state_kind);
    let mut state_buf = vec![0i64; n_state_leaves];
    unsafe {
        let seed = engine
            .get_function::<unsafe extern "C" fn(*mut i64)>("cantor_initial_state")
            .unwrap_or_else(|e| {
                eprintln!("internal error: could not find `cantor_initial_state`: {e}");
                process::exit(1);
            });
        seed.call(state_buf.as_mut_ptr());
    }

    let step = unsafe {
        engine
            .get_function::<unsafe extern "C" fn(*mut i64, *mut i64)>("cantor_step")
            .unwrap_or_else(|e| {
                eprintln!("internal error: could not find `cantor_step`: {e}");
                process::exit(1);
            })
    };

    let stdin = std::io::stdin();
    let mut lines = stdin.lock().lines();

    loop {
        let (event_ptr, is_final) = match lines.next() {
            Some(Ok(line)) => (encode_char_star(&line), false),
            Some(Err(e)) => {
                eprintln!("error reading stdin: {e}");
                process::exit(1);
            }
            None => (encode_eot_event(), true),
        };

        let mut in_buf = Vec::with_capacity(1 + n_state_leaves);
        in_buf.push(event_ptr);
        in_buf.extend_from_slice(&state_buf);

        let mut out_buf = vec![0i64; 1 + n_state_leaves];
        unsafe {
            step.call(in_buf.as_mut_ptr(), out_buf.as_mut_ptr());
        }

        println!("{}", format_char_vector(out_buf[0]));
        state_buf.copy_from_slice(&out_buf[1..]);

        if is_final {
            break;
        }
    }
}

/// Build a `Char*` (heap-allocated Arrow-backed vector) from a Rust `&str`,
/// one element per Unicode scalar value — the same runtime representation
/// JIT'd Cantor code itself builds array literals into, just called
/// directly since the driver runs as ordinary native Rust, not JIT'd code.
fn encode_char_star(s: &str) -> i64 {
    let builder = cantor::runtime::cantor_vec_builder_new_i64();
    for c in s.chars() {
        cantor::runtime::cantor_vec_builder_push_i64(builder, c as i64);
    }
    cantor::runtime::cantor_vec_builder_finish_i64(builder)
}

/// The synthetic final `Event` fed to an event-loop `main` when `stdin`
/// closes: a length-1 `Char*` containing codepoint 4 (ASCII EOT, the
/// traditional Ctrl-D "end of transmission" control character — not
/// U+2404 ␄, which is a printable *display glyph* for EOT and could
/// theoretically appear in real input). docs/design-decisions.md §6.
fn encode_eot_event() -> i64 {
    encode_char_star("\u{4}")
}

/// Decode a `Char` leaf (zero-extended to i64 by the trampoline, same
/// convention as `Unsigned32`) into its display form — the actual character,
/// not the bare codepoint. Only valid Unicode scalar values can ever reach
/// here: `char(n)` proves it once at construction, so `char::from_u32` is
/// infallible.
fn format_char(word: i64) -> String {
    let v = word as u32;
    let c = char::from_u32(v)
        .unwrap_or_else(|| panic!("ICE: Char leaf {v} is not a valid Unicode scalar"));
    format!("{c}")
}

/// Decode a `Char*` (`Vector(Char)`) pointer-as-i64 into its text — reuses
/// `Vector(Int)`'s `_i64` Arrow runtime verbatim (docs/design-decisions.md
/// §13). Shared by `format_kind_val`'s `Vector(Char)` arm and the
/// non-fallible scalar-main path below, which bypasses `format_kind_val`
/// entirely for any return Kind other than `Tuple`.
fn format_char_vector(vec_ptr: i64) -> String {
    let len = cantor::runtime::cantor_vec_len_i64(vec_ptr);
    (0..len)
        .map(|i| {
            let cp = cantor::runtime::cantor_vec_get_i64(vec_ptr, i) as u32;
            char::from_u32(cp)
                .unwrap_or_else(|| panic!("ICE: Char* element {cp} is not a valid Unicode scalar"))
        })
        .collect::<String>()
}

/// Decode a possibly-tagged `Int` word (int-soundness-plan phase 3 step 4b —
/// see `runtime/mod.rs`'s module doc for the encoding) into its decimal
/// display form.
fn format_tagged_int(word: i64) -> String {
    if word & 1 == 0 {
        (word >> 1).to_string()
    } else {
        let ptr = cantor::runtime::cantor_bigint_to_string(word);
        let s = unsafe { std::ffi::CStr::from_ptr(ptr as *const std::os::raw::c_char) };
        s.to_string_lossy().into_owned()
    }
}

fn count_kind_leaves(kind: &Kind) -> usize {
    match kind {
        Kind::Int | Kind::Int64 | Kind::Bool | Kind::Fail | Kind::Set(_) => 1,
        Kind::Signed32 | Kind::Unsigned32 | Kind::Char => 1,
        Kind::Tuple(elems) => elems.iter().map(count_kind_leaves).sum(),
        // TODO: tagged-union IR — count tag field + widest arm
        Kind::TaggedUnion(_) => 1,
        // A Vector is always a single pointer-as-i64 leaf, regardless of
        // element kind (see `codegen::wire::leaf_count`'s matching arm) —
        // decoding the pointed-to elements (`format_kind_val`) is the part
        // that's only implemented for `Char*` so far.
        Kind::Vector(_) => 1,
    }
}

fn format_kind_val(kind: &Kind, buf: &[i64], offset: &mut usize) -> String {
    match kind {
        Kind::Bool => {
            let v = buf[*offset] != 0;
            *offset += 1;
            format!("{v}")
        }
        Kind::Fail => {
            *offset += 1;
            "fail".to_string()
        }
        // int-soundness-plan phase 3 step 4b: `Int64`/`Set` leaves are
        // always a plain raw i64; an `Int` leaf is tagged and needs decoding.
        Kind::Int64 | Kind::Set(_) => {
            let v = buf[*offset];
            *offset += 1;
            format!("{v}")
        }
        // Signed32/Unsigned32 leaves already arrived sext/zext-ed to i64 by
        // the trampoline (docs/wrapping-and-quotient-sets-plan.md) — the
        // widened i64 already reads as the correct decimal value, no
        // decoding needed (never tagged, unlike `Kind::Int`).
        Kind::Signed32 | Kind::Unsigned32 => {
            let v = buf[*offset];
            *offset += 1;
            format!("{v}")
        }
        Kind::Char => {
            let v = buf[*offset];
            *offset += 1;
            format_char(v)
        }
        Kind::Int => {
            let v = buf[*offset];
            *offset += 1;
            format_tagged_int(v)
        }
        Kind::Tuple(elems) => {
            let parts: Vec<String> = elems
                .iter()
                .map(|k| format_kind_val(k, buf, offset))
                .collect();
            format!("({})", parts.join(", "))
        }
        // TODO: tagged-union IR — decode tag and display the active arm
        Kind::TaggedUnion(_) => {
            let v = buf[*offset];
            *offset += 1;
            format!("<tagged-union {v}>")
        }
        Kind::Vector(ek) if **ek == Kind::Char => {
            let vec_ptr = buf[*offset];
            *offset += 1;
            format_char_vector(vec_ptr)
        }
        Kind::Vector(_) => panic!("TODO: Kleene-star Vector kind not yet supported in CLI output"),
    }
}
