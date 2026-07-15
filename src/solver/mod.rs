//! Domain/range constraint checker using the cvc5 SMT solver.
//!
//! For each function signature `f : Domain -> Range` with body `f(x, ...) = expr`,
//! we ask cvc5 to refute:
//!   ∃ params satisfying Domain. expr(params) ∉ Range
//!
//! UNSAT → proved for all inputs. SAT → counterexample returned.
//!
//! **Interprocedural checking (contract-based / modular)**
//! When the body contains a call `g(args)`, we do NOT inline `g`'s body.
//! Instead, for each of `g`'s signatures `g : A -> B` we assert:
//!   args ∈ A  →  result_of_call ∈ B
//! The solver reasons about `result_of_call` only through these contracts.
//! This handles recursion correctly (own signature = induction hypothesis)
//! and respects the library-boundary compilation model (§7).
//!
//! Current limitations (lifted as the language grows):
//! - Only named built-in sets as domain/range (`Int`, `Nat`, `NatPos`, `NonZeroInt`, `IntN`).
//! - Only integer-sorted parameters and return values.

mod blocks;
mod constrained;
mod disjointness;
mod encode;
mod encode_call;
mod encode_ctrl;
mod event_loop;
mod int64_split;
mod loops;
mod membership;
mod membership_seq;
mod obligations;
mod preds;
mod sig_check;
mod sort;

pub use constrained::ConstrainedTree;

use std::collections::HashMap;
use std::sync::Mutex;

use cvc5::{Kind, Term, TermManager};

use crate::{
    ast::Item,
    semantics::{
        elaborate::elaborate,
        tree::{SemExpr, SemFunctionBody, SemFunctionDef, SemItem, SemNameDef},
    },
    span::{Span, Symbol},
};

/// Map from name to its elaborated `SemNameDef` — built once per `check_file`
/// call from `elaborate()`'s output. Unlike codegen, the solver needs the
/// full elaborated value (not just `Kind`) for expanding aliases and
/// evaluating annotated constants during encoding.
pub(crate) type NameDefs = HashMap<Symbol, SemNameDef>;

use self::disjointness::{check_overload_disjointness, validate_disjoint_unions};
use self::encode::{EncodeCtx, Env, boolean_value, encode_expr, integer_value};
use self::event_loop::validate_event_loop_main;
use self::membership::{Membership, membership_constraint};
use self::obligations::{BuiltinObligation, OverflowObligation};
use self::preds::{
    build_distinct_preds, build_solver_preds, build_wrapping_preds, validate_equiv_decls,
    validate_quotient_sets,
};
use self::sig_check::{SideChannels, check_block_sig, check_sig, configured_solver};

// ── Public types ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
pub enum CheckResult {
    /// Every input satisfying the domain maps to an output in the range,
    /// and no built-in operation can produce undefined behaviour.
    Proved,
    /// The solver found concrete parameter values that violate a safety
    /// obligation.  `reason` is a human-readable explanation such as
    /// `"not in Nat"` (range violation) or `"division by zero"`.
    Counterexample {
        params: HashMap<String, i64>,
        output: i64,
        reason: String,
    },
    /// Could not determine (unsupported construct, solver timeout, etc.).
    Unknown(String),
}

/// int-soundness-plan phase 2: multiple `FunctionDef`s may share a name (an
/// overload set), so every name maps to a `Vec` of definitions — in file
/// order, since call-resolution indices (`ConstrainedTree::overload_resolution`)
/// and codegen's mangled-name table both derive an overload's identity from
/// its position in this same ordering. The overwhelmingly common case is a
/// `Vec` of length 1.
type FunctionEnv<'a> = HashMap<Symbol, Vec<&'a SemFunctionDef>>;

/// Result of checking a whole file: either every obligation was proved
/// (yielding a [`ConstrainedTree`] — see there for why that's the only way
/// to construct one), or at least one signature has a `Counterexample` or
/// `Unknown` result somewhere, in which case the full per-signature report
/// is returned unchanged so callers can still display it.
///
/// This is distinct from `check_file`'s outer `Result`'s `Err` arm, which is
/// reserved for a hard `CompileError` (elaboration/internal failure) —
/// "not every obligation proved" is not a failure of `check_file` itself.
pub enum CheckOutcome {
    Proved(ConstrainedTree),
    NotProved(Vec<(String, Vec<(String, CheckResult)>)>),
}

// ── Public entry points ───────────────────────────────────────────────────────

// TODO: make a struct with member functions to hold things like timeout_ms

/// Check every function in a parsed file, using each function's signature as
/// a contract available to all other functions in the file.
///
/// Returns one entry per function, each containing one result per signature.
///
/// `timeout_ms` is applied as the `tlimit` option on every fresh solver
/// instance.  Pass `0` to disable the limit entirely.
///
/// Returns `Ok(CheckOutcome::Proved(tree))` only when every signature in the
/// file resolved to `CheckResult::Proved` — that `ConstrainedTree` is the
/// only handle `codegen::compile_constrained` accepts, so a program can only
/// be compiled once this function has verified it in full.
///
/// cvc5 is not safe to call concurrently from multiple threads, even when
/// each thread uses its own independent `TermManager`/`Solver` — the
/// underlying C++ library has global state that data-races across threads
/// (observed here as a segfault when `cargo test` ran the solver test suite
/// in parallel; see e.g. https://github.com/CVC4/CVC4/issues/3456 for the
/// same failure class upstream). This lock serializes every call through
/// the one production entry point into cvc5 so callers can still use
/// ordinary threads/parallel test runners around it safely.
static CVC5_CALL_LOCK: Mutex<()> = Mutex::new(());

pub fn check_file(
    items: &[Item],
    timeout_ms: u64,
) -> Result<CheckOutcome, crate::error::CompileError> {
    let _cvc5_guard = CVC5_CALL_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let sem_items = elaborate(items)?;

    let name_defs: NameDefs = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::NameDef(def) => Some((def.name.clone(), def.clone())),
            _ => None,
        })
        .collect();

    // int-soundness-plan phase 3 (step 4a): replaces an eligible `Int -> Int`
    // `SemItem::FunctionDef` with its compiler-generated `Int64`/`BigInt`
    // overload pair whenever the solver proves it's sound to (see
    // `int64_split`'s module doc) — everything below this point sees the
    // (possibly split) result and treats it exactly like an ordinary
    // phase 2 overload set, unchanged.
    let sem_items = int64_split::generate_int64_bigint_splits(sem_items, &name_defs, timeout_ms);

    let mut fn_env: FunctionEnv<'_> = FunctionEnv::new();
    for item in &sem_items {
        if let SemItem::FunctionDef(def) = item {
            fn_env.entry(def.name.clone()).or_default().push(def);
        }
    }

    // MVP IO event loop (docs/design-decisions.md §6): a structural/shape
    // check on `main`, not a proof obligation — short-circuits here via `?`
    // rather than folding into `results` below. No-op for files that don't
    // declare an event-loop-shaped `main` at all.
    validate_event_loop_main(&fn_env)?;

    // Overflow-check outcomes (int-soundness-plan phase 1) live entirely
    // outside `results`/`CheckResult`/`all_proved` below — an unproved one
    // must not block compilation (that's the whole point of phase 1: a
    // counterexample/unknown overflow claim degrades to a runtime check, not
    // a compile error). One map shared across every function in the file;
    // spans are unique per source location so there's no cross-function
    // collision. Only meaningful (and only consulted by codegen) once the
    // file is otherwise `Proved` — see below.
    let mut overflow_checks: HashMap<Span, bool> = HashMap::new();

    // Overload call-resolution outcomes (int-soundness-plan phase 2): same
    // side-channel shape as `overflow_checks` but keeps `Option<usize>` while
    // accumulating (see `decide_overload_resolutions`'s unanimous-agreement
    // merge) — only converted to the `HashMap<Span, usize>` `ConstrainedTree`
    // exposes once every function has been checked, below.
    let mut overload_resolutions: HashMap<Span, Option<usize>> = HashMap::new();

    let mut results: Vec<(String, Vec<(String, CheckResult)>)> = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::FunctionDef(def) => {
                let results = check_function(
                    def,
                    &fn_env,
                    &name_defs,
                    timeout_ms,
                    &mut overflow_checks,
                    &mut overload_resolutions,
                );
                Some(results.map(|r| (def.name.0.clone(), r)))
            }
            SemItem::NameDef(def) => {
                // Only annotated defs (`name : Set = value`) produce a check result.
                let ty = def.ty.as_ref()?;
                let result = check_name_def(def, ty, &fn_env, &name_defs, timeout_ms);
                let label = format!("{} : {} = {}", def.name, ty, def.value);
                Some(Ok((def.name.0.clone(), vec![(label, result)])))
            }
            // Checked separately below (`validate_equiv_decls`), once
            // `fn_env` covers every function in the file — not per-item here.
            SemItem::EquivDecl { .. } => None,
        })
        .collect::<Result<_, _>>()?;

    // int-soundness-plan phase 2: overload domains must be provably disjoint
    // — unlike overflow/resolution, this *does* gate `all_proved` below (an
    // ordinary proof obligation, reusing the domain/range checker, not a new
    // escape hatch). Differing-arity overloads of the same name need no
    // check against each other (arity alone already makes them disjoint).
    results.extend(check_overload_disjointness(&fn_env, &name_defs, timeout_ms));

    // Quotient sets (docs/wrapping-and-quotient-sets-plan.md's Feature 2):
    // canonicalizer signature containment and idempotence, proved once here
    // rather than re-proved per call site — same "gates `all_proved`, no
    // `assume` escape" treatment as overload disjointness just above.
    results.extend(validate_quotient_sets(&name_defs, &fn_env, timeout_ms));

    // Function equivalence checking (`equiv f, g`) — a new kind of claim
    // (two existing functions agree on their shared domain), same
    // "gates `all_proved`, no `assume` escape" treatment as the two above.
    results.extend(validate_equiv_decls(
        &sem_items, &name_defs, &fn_env, timeout_ms,
    ));

    let all_proved = results
        .iter()
        .all(|(_, sig_results)| sig_results.iter().all(|(_, r)| *r == CheckResult::Proved));

    if all_proved {
        let overload_resolution: HashMap<Span, usize> = overload_resolutions
            .into_iter()
            .filter_map(|(span, resolved)| resolved.map(|idx| (span, idx)))
            .collect();
        Ok(CheckOutcome::Proved(ConstrainedTree {
            items: items.to_vec(),
            sem_items,
            results,
            overflow_checks,
            overload_resolution,
        }))
    } else {
        Ok(CheckOutcome::NotProved(results))
    }
}

/// Check one function definition against its signatures.
///
/// `fn_env` provides the contracts of all other (and the same) functions
/// reachable from this function's body.
pub fn check_function(
    def: &SemFunctionDef,
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
    overflow_checks: &mut HashMap<Span, bool>,
    overload_resolutions: &mut HashMap<Span, Option<usize>>,
) -> Result<Vec<(String, CheckResult)>, crate::error::CompileError> {
    let param_names: Vec<Symbol> = def.params.iter().map(|p| p.name.clone()).collect();

    Ok(def
        .sigs
        .iter()
        .enumerate()
        .map(|(i, sig)| {
            let label = sig_label(&def.name.0, i, def.sigs.len());
            let mut channels = SideChannels {
                overflow_checks,
                overload_resolutions,
            };
            let result = match &def.body {
                SemFunctionBody::Expr(body) => check_sig(
                    sig,
                    &param_names,
                    body,
                    fn_env,
                    name_defs,
                    timeout_ms,
                    &mut channels,
                ),
                SemFunctionBody::Block(stmts) => check_block_sig(
                    sig,
                    &param_names,
                    stmts,
                    fn_env,
                    name_defs,
                    timeout_ms,
                    &mut channels,
                ),
            };
            (label, result)
        })
        .collect())
}

fn sig_label(name: &str, idx: usize, total: usize) -> String {
    if total == 1 {
        name.to_owned()
    } else {
        format!("{name} (sig {})", idx + 1)
    }
}

fn check_name_def(
    def: &SemNameDef,
    ty: &SemExpr,
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> CheckResult {
    if let Some(result) = validate_disjoint_unions(ty, name_defs, timeout_ms) {
        return result;
    }
    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);

    let distinct_preds = build_solver_preds(&tm, name_defs, fn_env);
    let env = Env::new();
    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    // Top-level `name : Set = value` constants are constant-folded by
    // codegen's separate `eval_const` pass, never compiled through
    // `compile_arith` — so there's no codegen site to consult an overflow
    // verdict here. Collected (encode_expr requires the accumulator
    // unconditionally) but deliberately never decided/merged anywhere.
    let mut overflow_obligs: Vec<OverflowObligation<'_>> = Vec::new();
    // Same rationale as `overflow_obligs` just above: collected because
    // `encode_expr` requires the accumulator unconditionally, never decided.
    let mut overload_obligs: Vec<self::obligations::OverloadCallObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);

    let mut encode_ctx = EncodeCtx {
        name_defs,
        fn_env,
        tm: &tm,
        solver: &mut solver,
        call_counter: &mut call_counter,
        builtin_obligs: &mut builtin_obligs,
        overflow_obligs: &mut overflow_obligs,
        overload_obligs: &mut overload_obligs,
        distinct_preds: &distinct_preds,
    };
    let value_term = match encode_expr(&def.value, &env, &mut encode_ctx, top_guard, None) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let range_obligation =
        match membership_constraint(&tm, value_term, ty, name_defs, &distinct_preds) {
            Membership::Unconstrained => None,
            Membership::Constrained(c) => Some(c),
            Membership::Unsupported => {
                return CheckResult::Unknown("unsupported set annotation".into());
            }
        };

    // Constant values can contain built-in obligations too (`/` divisor,
    // call-site domains, …) — they must be discharged, not dropped.
    let mut all_obligations: Vec<Term<'_>> = builtin_obligs
        .iter()
        .map(|o| {
            if o.path_cond.to_string().trim() == "true" {
                o.obligation.clone()
            } else {
                tm.mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
            }
        })
        .collect();
    if let Some(rc) = range_obligation {
        all_obligations.push(rc);
    }
    if all_obligations.is_empty() {
        return CheckResult::Proved;
    }

    let combined = if all_obligations.len() == 1 {
        all_obligations.remove(0)
    } else {
        tm.mk_term(Kind::And, &all_obligations)
    };
    solver.assert_formula(tm.mk_term(Kind::Not, &[combined]));

    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        let reason = builtin_obligs
            .iter()
            .find(|o| {
                boolean_value(&solver.get_value(o.path_cond.clone()))
                    && !boolean_value(&solver.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string())
            .unwrap_or_else(|| format!("constant value not in {}", ty));
        CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason,
        }
    } else {
        CheckResult::Unknown("solver returned unknown".into())
    }
}
