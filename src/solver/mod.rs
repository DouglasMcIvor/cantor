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
mod sort;

pub use constrained::ConstrainedTree;

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::Item,
    semantics::{
        elaborate::elaborate,
        tree::{
            SemExpr, SemFunctionBody, SemFunctionDef, SemFunctionSig, SemItem, SemNameDef,
            sem_param_set_exprs,
        },
    },
    span::{Span, Symbol},
};

/// Map from name to its elaborated `SemNameDef` — built once per `check_file`
/// call from `elaborate()`'s output. Unlike codegen, the solver needs the
/// full elaborated value (not just `Kind`) for expanding aliases and
/// evaluating annotated constants during encoding.
pub(crate) type NameDefs = HashMap<Symbol, SemNameDef>;

use crate::kind::Kind as ValKind;

use self::blocks::{BlockCtx, body_has_unconstrained_loop_var, encode_block};
use self::disjointness::{check_overload_disjointness, validate_disjoint_unions};
use self::encode::{
    EncodeCtx, Env, boolean_value, encode_expr, integer_value, mk_decomposed_tuple,
};
use self::event_loop::validate_event_loop_main;
use self::membership::{Membership, SolverPreds, membership_constraint};
use self::obligations::{
    BuiltinObligation, OverflowObligation, decide_overflow_obligations, decide_overload_resolutions,
};
use self::preds::{
    build_distinct_preds, build_solver_preds, build_wrapping_preds, validate_equiv_decls,
    validate_quotient_sets,
};
use self::sort::set_sort;

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

// ── Shared setup/teardown for both signature checkers ────────────────────────
//
// check_sig (pure expression body) and check_block_sig (block body) both:
// configure a fresh solver, build each parameter's solver constant from the
// domain (decomposing tuples into leaf constants), then — after the body is
// encoded by whichever encoder fits the body shape — combine the range
// obligation with any built-in obligations and decode the solver's model into
// a CheckResult. Only the body-encoding step itself differs (encode_expr vs
// encode_block, plus check_block_sig's loop-invariant Unknown carve-out).

/// Configure a solver with the options both checkers need.
/// The single source of cvc5 option configuration for *every* solver
/// instance this module creates — the main per-function solver as well as
/// every isolated sub-query solver (`check_require`, `check_loop_inductive_step`,
/// `validate_disjoint_unions`, `check_name_def`'s constant check, …). Call
/// this rather than hand-rolling `Solver::new` + `set_option` calls: a prior
/// version of this codebase had two sub-query call sites that duplicated
/// this list by hand and silently dropped `mbqi`, which made cvc5 report
/// `Unknown` for completely unrelated counterexample queries whenever a
/// quantified `X*` domain fact merely happened to be in scope (see
/// `docs/design-decisions.md`'s "for x in S loops" section for the
/// post-mortem). One function, called everywhere, closes off that whole
/// class of bug.
fn configured_solver<'tm>(tm: &'tm TermManager, timeout_ms: u64) -> Solver<'tm> {
    let mut solver = Solver::new(tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    // nl-cov (libpoly-based covering/CAD) replaces cvc5's default heuristic
    // nonlinear-arithmetic engine, which can hang for minutes on self-multiplication
    // bounds checks (`x * x` against an Int32/Int64-sized range) — see
    // docs/design-decisions.md's nl-cov note.
    solver.set_option("nl-cov", "true");
    if timeout_ms > 0 {
        solver.set_option("tlimit", &timeout_ms.to_string());
    }
    solver
}

/// Build each parameter's solver constant from `domain`, asserting its
/// domain-membership constraint onto `solver`. Tuple params are decomposed
/// into leaf scalar constants assembled with `mk_tuple` — this ensures
/// `TupleProject` in the body always operates on a concrete constructor term
/// (not a symbolic tuple constant), which cvc5's arithmetic beta-reduction
/// requires. Returns `(domain_parts, param_terms)`, both in parameter order —
/// callers need `domain_parts` again later to decode counterexample witnesses
/// by Kind.
fn build_param_terms<'tm, 'e>(
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    domain: Option<&'e SemExpr>,
    param_names: &[Symbol],
    distinct_preds: &SolverPreds<'tm>,
    name_defs: &NameDefs,
) -> Result<(Vec<&'e SemExpr>, Vec<Term<'tm>>), CheckResult> {
    let domain_parts: Vec<&SemExpr> =
        sem_param_set_exprs(domain, param_names.len()).map_err(CheckResult::Unknown)?;

    let mut param_terms: Vec<Term<'_>> = Vec::new();
    for (n, part) in param_names.iter().zip(domain_parts.iter()) {
        let k = part.kind_of.clone();
        if matches!(k, ValKind::Tuple(_)) {
            let (assembled, leaves) =
                mk_decomposed_tuple(tm, &n.0, part, distinct_preds, name_defs);
            for (leaf, leaf_set) in leaves {
                match membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return Err(CheckResult::Unknown(
                            "unsupported domain set expression".into(),
                        ));
                    }
                }
            }
            param_terms.push(assembled);
        } else {
            let sort = match set_sort(tm, part, distinct_preds, name_defs) {
                Some(s) => s,
                None => {
                    return Err(CheckResult::Unknown(format!(
                        "parameter `{}` has an unsupported domain sort (internal error)",
                        n.0
                    )));
                }
            };
            let term = tm.mk_const(sort, &n.0);
            if k != ValKind::Bool {
                match membership_constraint(tm, term.clone(), part, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return Err(CheckResult::Unknown(
                            "unsupported domain set expression".into(),
                        ));
                    }
                }
            }
            param_terms.push(term);
        }
    }

    Ok((domain_parts, param_terms))
}

/// Decode each parameter's solver-model value into the `i64` shown in a
/// `CheckResult::Counterexample`'s `params` map, keyed by Kind.
fn decode_cex_params<'tm>(
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    domain_parts: &[&SemExpr],
    distinct_preds: &SolverPreds<'tm>,
) -> HashMap<String, i64> {
    let mut cex_params = HashMap::new();
    for ((name, term), part) in param_names
        .iter()
        .zip(param_terms.iter())
        .zip(domain_parts.iter())
    {
        let val = solver.get_value(term.clone());
        let k = part.kind_of.clone();
        let n = if k == ValKind::Bool {
            boolean_value(&val) as i64
        } else if matches!(
            k,
            ValKind::Tuple(_) | ValKind::TaggedUnion(_) | ValKind::Vector(_)
        ) {
            // TODO: render tuple/datatype-arm/vector model values in counterexample display
            0
        } else if let Some(info) = distinct_preds
            .wrapping
            .values()
            .find(|i| i.d_sort == term.sort())
        {
            // Parameter has a wrapping (Signed32/Unsigned32) sort — apply
            // `from_D` to recover the BitVec, then the signed/unsigned
            // BitVec→Int reading to get the same decimal value `from(x)`
            // would print.
            let bv_app = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), term.clone()]);
            let to_int_kind = if info.signed {
                Kind::BitvectorSbvToInt
            } else {
                Kind::BitvectorUbvToInt
            };
            let int_app = tm.mk_term(to_int_kind, &[bv_app]);
            integer_value(&solver.get_value(int_app))
        } else if let Some(info) = distinct_preds.values().find(|i| i.sort == term.sort()) {
            // Parameter has a distinct (uninterpreted) sort — apply `from_D` to
            // recover the underlying integer for the counterexample display.
            let from_app = tm.mk_term(Kind::ApplyUf, &[info.from.clone(), term.clone()]);
            integer_value(&solver.get_value(from_app))
        } else {
            integer_value(&val)
        };
        cex_params.insert(name.0.clone(), n);
    }
    cex_params
}

/// The two file-wide proof side-channels (int-soundness-plan phases 1 and 2)
/// threaded through `check_sig`/`check_block_sig`, bundled to keep those
/// functions under clippy's argument-count limit — same fix as the
/// `EncodeCtx`/`BlockCtx`/`LoopCtx` family (see project history).
struct SideChannels<'a> {
    overflow_checks: &'a mut HashMap<Span, bool>,
    overload_resolutions: &'a mut HashMap<Span, Option<usize>>,
}

/// The solver-wide pieces `finish_check`/`decode_cex_params` need, common to
/// both `check_sig` and `check_block_sig`.
struct CheckCtx<'a, 'tm> {
    tm: &'tm TermManager,
    solver: &'a mut Solver<'tm>,
    name_defs: &'a NameDefs,
    distinct_preds: &'a SolverPreds<'tm>,
}

/// One signature's parameter names/solver terms/domain parts, always indexed
/// in parallel — bundled since every consumer (`finish_check`,
/// `decode_cex_params`) reads all three together.
struct SigParams<'a, 'tm> {
    names: &'a [Symbol],
    terms: &'a [Term<'tm>],
    domain_parts: &'a [&'a SemExpr],
}

/// Shared tail of both signature checkers: combine the range obligation with
/// any built-in obligations, ask the solver to refute their conjunction, and
/// turn the result into a `CheckResult`. `extra_unknown_check` runs only on
/// the SAT (counterexample) path, before decoding witness params — it lets
/// `check_block_sig` report its loop-invariant-specific `Unknown` message
/// instead of a generic counterexample when that's the real cause.
fn finish_check<'tm>(
    ctx: &mut CheckCtx<'_, 'tm>,
    body_term: Term<'tm>,
    range: &SemExpr,
    builtin_obligs: &[BuiltinObligation<'tm>],
    params: &SigParams<'_, 'tm>,
    extra_unknown_check: impl FnOnce() -> Option<CheckResult>,
) -> CheckResult {
    let range_obligation = match membership_constraint(
        ctx.tm,
        body_term.clone(),
        range,
        ctx.name_defs,
        ctx.distinct_preds,
    ) {
        Membership::Unconstrained => None,
        Membership::Constrained(c) => Some(c),
        Membership::Unsupported => {
            return CheckResult::Unknown("unsupported range set expression".into());
        }
    };

    let builtin_formulas: Vec<Term<'_>> = builtin_obligs
        .iter()
        .map(|o| {
            if o.path_cond.to_string().trim() == "true" {
                o.obligation.clone()
            } else {
                ctx.tm
                    .mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
            }
        })
        .collect();

    let mut all_obligations: Vec<Term<'_>> = builtin_formulas;
    if let Some(rc) = range_obligation {
        all_obligations.push(rc);
    }

    if all_obligations.is_empty() {
        return CheckResult::Proved;
    }

    let combined = if all_obligations.len() == 1 {
        all_obligations.remove(0)
    } else {
        ctx.tm.mk_term(Kind::And, &all_obligations)
    };
    ctx.solver
        .assert_formula(ctx.tm.mk_term(Kind::Not, &[combined]));

    let sat = ctx.solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        if let Some(early) = extra_unknown_check() {
            return early;
        }
        let cex_params = decode_cex_params(
            ctx.tm,
            ctx.solver,
            params.names,
            params.terms,
            params.domain_parts,
            ctx.distinct_preds,
        );
        let reason = builtin_obligs
            .iter()
            .find(|o| {
                boolean_value(&ctx.solver.get_value(o.path_cond.clone()))
                    && !boolean_value(&ctx.solver.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string())
            .unwrap_or_else(|| format!("not in {}", range));
        let output_term = ctx.solver.get_value(body_term);
        CheckResult::Counterexample {
            params: cex_params,
            output: integer_value(&output_term),
            reason,
        }
    } else {
        CheckResult::Unknown("solver returned unknown".into())
    }
}

/// Every `?`-ed call site in a body requires the *caller's own* declared
/// range to include whichever propagation tag(s) (`Fail`/`None`) the
/// callee's range can produce. Without this, an out-of-contract `?` (e.g.
/// calling a `Nat | None`-returning function from inside a plain `Nat`
/// function) would still "prove" fine — nothing in `encode_call`'s
/// narrowing logic depends on the caller's own range — and then crash
/// codegen with an LLVM return-type mismatch ICE instead of failing here
/// with a clear diagnostic. Mirrors `encode_call`'s own "first
/// arity-matching candidate, first signature" MVP simplification (an
/// overloaded/multi-signature callee is checked only via its first match,
/// same as `narrow_try` itself).
fn check_try_propagation<'a>(
    try_calls: impl Iterator<Item = (&'a Symbol, Span)>,
    sig_range: &SemExpr,
    fn_env: &FunctionEnv<'_>,
) -> Option<CheckResult> {
    use crate::semantics::tree::{range_contains_fail, range_contains_none};
    for (callee, _span) in try_calls {
        let Some(callee_sig) = fn_env
            .get(callee)
            .and_then(|defs| defs.first())
            .and_then(|def| def.sigs.first())
        else {
            continue; // undefined/malformed callee — reported elsewhere
        };
        let missing_fail =
            range_contains_fail(&callee_sig.range) && !range_contains_fail(sig_range);
        let missing_none =
            range_contains_none(&callee_sig.range) && !range_contains_none(sig_range);
        if !missing_fail && !missing_none {
            continue;
        }
        let missing = match (missing_fail, missing_none) {
            (true, true) => "`Fail` and `None`",
            (true, false) => "`Fail`",
            (false, true) => "`None`",
            (false, false) => unreachable!("checked above"),
        };
        return Some(CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: format!(
                "`{}(...)?` can propagate {missing}, but this function's own return type \
                 does not include {missing} — add it to the return type",
                callee.0
            ),
        });
    }
    None
}

// ── Block body checker ────────────────────────────────────────────────────────

fn check_block_sig(
    sig: &SemFunctionSig,
    param_names: &[Symbol],
    stmts: &[crate::semantics::tree::SemStmt],
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
    channels: &mut SideChannels<'_>,
) -> CheckResult {
    if let Some(dom) = &sig.domain
        && let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms)
    {
        return result;
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) {
        return result;
    }

    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_solver_preds(&tm, name_defs, fn_env);

    let (domain_parts, param_terms) = match build_param_terms(
        &tm,
        &mut solver,
        sig.domain.as_ref(),
        param_names,
        &distinct_preds,
        name_defs,
    ) {
        Ok(v) => v,
        Err(e) => return e,
    };

    let mut env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let mut overflow_obligs: Vec<OverflowObligation<'_>> = Vec::new();
    let mut overload_obligs: Vec<self::obligations::OverloadCallObligation<'_>> = Vec::new();
    let mut ssa_counter = 0usize;
    let mut constraint_env: HashMap<Symbol, SemExpr> = HashMap::new();
    // Seed constraint_env with each Set(_)/Vector(_)-kind parameter's declared
    // range, so `for x in a_param` can extract the element-kind hypothesis
    // the same way a `mut`-local Set/Vector binding already does (see
    // `blocks.rs`'s `MutLet` arms) — otherwise `check_for_inductive_step`
    // only sees the bare parameter name and has no way to recover its range.
    for (name, part) in param_names.iter().zip(domain_parts.iter()) {
        if matches!(part.kind_of, ValKind::Set(_) | ValKind::Vector(_)) {
            constraint_env.insert(name.clone(), (*part).clone());
        }
    }
    let mut has_runtime_assert = false;
    let mut immutable_names: HashSet<Symbol> = HashSet::new();

    let result_sort = set_sort(&tm, &sig.range, &distinct_preds, name_defs);
    let mut block_ctx = BlockCtx {
        encode: EncodeCtx {
            name_defs,
            fn_env,
            tm: &tm,
            solver: &mut solver,
            call_counter: &mut call_counter,
            builtin_obligs: &mut builtin_obligs,
            overflow_obligs: &mut overflow_obligs,
            overload_obligs: &mut overload_obligs,
            distinct_preds: &distinct_preds,
        },
        ssa_counter: &mut ssa_counter,
        param_names,
        param_terms: &param_terms,
        constraint_env: &mut constraint_env,
        has_runtime_assert: &mut has_runtime_assert,
        immutable_names: &mut immutable_names,
        overflow_checks: channels.overflow_checks,
        overload_resolutions: channels.overload_resolutions,
        timeout_ms,
    };
    let body_term = match encode_block(stmts, &mut env, &mut block_ctx, result_sort) {
        Ok(Some(t)) => t,
        Ok(None) => {
            return CheckResult::Unknown("block body has no return expression".into());
        }
        Err(early) => return early,
    };

    // Decide this signature's flat-statement overflow obligations now, against
    // `solver` as it stands — before `finish_check` asserts the negated
    // correctness goal, which (once proved) would leave `solver` inconsistent
    // and every later query vacuously "proved". Loop bodies already decided
    // their own overflow obligations inline (see `loops.rs`), directly into
    // `overflow_checks`, since they run on an isolated temp solver.
    decide_overflow_obligations(
        &overflow_obligs,
        &tm,
        &solver,
        channels.overflow_checks,
        timeout_ms,
    );
    decide_overload_resolutions(
        &overload_obligs,
        &tm,
        &solver,
        channels.overload_resolutions,
        timeout_ms,
    );

    if has_runtime_assert && !crate::semantics::tree::range_contains_fail(&sig.range) {
        return CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: "assert may fail at runtime but return type does not include `Fail` \
                     — add `| Fail` or use `!!` on the return type, or prove the assertion statically"
                .into(),
        };
    }
    let mut try_calls = Vec::new();
    crate::semantics::tree::collect_try_calls_stmts(stmts, &mut try_calls);
    if let Some(result) = check_try_propagation(try_calls.into_iter(), &sig.range, fn_env) {
        return result;
    }

    let mut check_ctx = CheckCtx {
        tm: &tm,
        solver: &mut solver,
        name_defs,
        distinct_preds: &distinct_preds,
    };
    let sig_params = SigParams {
        names: param_names,
        terms: &param_terms,
        domain_parts: &domain_parts,
    };
    finish_check(
        &mut check_ctx,
        body_term,
        &sig.range,
        &builtin_obligs,
        &sig_params,
        || {
            body_has_unconstrained_loop_var(stmts, &constraint_env, &tm, name_defs, &distinct_preds)
                .then(|| {
                    CheckResult::Unknown(
                        "while loop: declare all mutable variable constraints \
                     (`mut name: Set = expr`) to enable counterexample extraction"
                            .into(),
                    )
                })
        },
    )
}

// ── Pure expression body checker ──────────────────────────────────────────────

fn check_sig(
    sig: &SemFunctionSig,
    param_names: &[Symbol],
    body: &SemExpr,
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
    channels: &mut SideChannels<'_>,
) -> CheckResult {
    if let Some(dom) = &sig.domain
        && let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms)
    {
        return result;
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) {
        return result;
    }

    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_solver_preds(&tm, name_defs, fn_env);

    let (domain_parts, param_terms) = match build_param_terms(
        &tm,
        &mut solver,
        sig.domain.as_ref(),
        param_names,
        &distinct_preds,
        name_defs,
    ) {
        Ok(v) => v,
        Err(e) => return e,
    };

    let env: Env<'_> = param_names
        .iter()
        .cloned()
        .zip(param_terms.iter().cloned())
        .collect();

    let mut call_counter = 0usize;
    let mut builtin_obligs: Vec<BuiltinObligation<'_>> = Vec::new();
    let mut overflow_obligs: Vec<OverflowObligation<'_>> = Vec::new();
    let mut overload_obligs: Vec<self::obligations::OverloadCallObligation<'_>> = Vec::new();
    let top_guard = tm.mk_boolean(true);
    let range_sort = set_sort(&tm, &sig.range, &distinct_preds, name_defs);
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
    let body_term = match encode_expr(body, &env, &mut encode_ctx, top_guard, range_sort) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let mut try_calls = Vec::new();
    crate::semantics::tree::collect_try_calls_expr(body, &mut try_calls);
    if let Some(result) = check_try_propagation(try_calls.into_iter(), &sig.range, fn_env) {
        return result;
    }

    // See `check_block_sig`'s identical comment: must run before `finish_check`'s
    // negated-goal assertion.
    decide_overflow_obligations(
        &overflow_obligs,
        &tm,
        &solver,
        channels.overflow_checks,
        timeout_ms,
    );
    decide_overload_resolutions(
        &overload_obligs,
        &tm,
        &solver,
        channels.overload_resolutions,
        timeout_ms,
    );

    let mut check_ctx = CheckCtx {
        tm: &tm,
        solver: &mut solver,
        name_defs,
        distinct_preds: &distinct_preds,
    };
    let sig_params = SigParams {
        names: param_names,
        terms: &param_terms,
        domain_parts: &domain_parts,
    };
    finish_check(
        &mut check_ctx,
        body_term,
        &sig.range,
        &builtin_obligs,
        &sig_params,
        || None,
    )
}
