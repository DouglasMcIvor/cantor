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
mod encode;
mod encode_call;
mod loops;
mod membership;
mod sort;

pub use constrained::ConstrainedTree;

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{DefKind, Item},
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
use self::encode::{
    BuiltinObligation, EncodeCtx, Env, OverflowObligation, boolean_value,
    decide_overflow_obligations, encode_expr, integer_value, mk_decomposed_tuple,
};
use self::membership::{DistinctInfo, DistinctPreds, Membership, membership_constraint};
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

// ── Distinct predicate builder ────────────────────────────────────────────────

/// For each `D = distinct B` in `name_defs`, create a CVC5 uninterpreted sort plus
/// constructor/destructor uninterpreted functions:
///   - `sort  = mk_uninterpreted_sort("D")`
///   - `mk_D  : Int → D_sort`  (wraps an integer as a D-value)
///   - `from_D: D_sort → Int`  (extracts the underlying integer)
///
/// No global axioms are needed; basis constraints are emitted on-demand when
/// `litre(n)` or `from(x)` is encoded.
///
/// `Fail` is registered here too, as a builtin distinct sort — it never
/// appears in `name_defs` (it's resolved via `builtins::lookup`, not a user
/// definition), so it's added unconditionally alongside the user-defined
/// ones. This is the only Fail-specific step in the whole cross-kind union
/// pipeline: once `Fail` has its own uninterpreted CVC5 sort, every other
/// piece (cross-kind detection in `set_sort`, datatype construction in
/// `build_union_datatype_sort`, membership, coercion) already treats any
/// distinct-sort arm generically, so `Int | Fail` / `Int | (Fail * Y)` need
/// no Fail-specific code beyond this registration. See
/// docs/design-decisions.md §13 ("Solver representation of `Fail`").
fn build_distinct_preds<'tm>(tm: &'tm TermManager, name_defs: &NameDefs) -> DistinctPreds<'tm> {
    let user_defined = name_defs
        .iter()
        .filter(|(_, def)| def.kind == DefKind::Distinct)
        .map(|(sym, _)| sym.clone());
    let with_fail = user_defined.chain(std::iter::once(Symbol::new("Fail")));

    with_fail
        .map(|sym| {
            let sort = tm.mk_uninterpreted_sort(&sym.0);
            let mk = tm.mk_const(
                tm.mk_fun_sort(&[tm.integer_sort()], sort.clone()),
                &format!("mk_{}", sym.0),
            );
            let from = tm.mk_const(
                tm.mk_fun_sort(std::slice::from_ref(&sort), tm.integer_sort()),
                &format!("from_{}", sym.0),
            );
            (sym, DistinctInfo { sort, mk, from })
        })
        .collect()
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

    let mut fn_env: FunctionEnv<'_> = FunctionEnv::new();
    for item in &sem_items {
        if let SemItem::FunctionDef(def) = item {
            fn_env.entry(def.name.clone()).or_default().push(def);
        }
    }

    let name_defs: NameDefs = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::NameDef(def) => Some((def.name.clone(), def.clone())),
            _ => None,
        })
        .collect();

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
        })
        .collect::<Result<_, _>>()?;

    // int-soundness-plan phase 2: overload domains must be provably disjoint
    // — unlike overflow/resolution, this *does* gate `all_proved` below (an
    // ordinary proof obligation, reusing the domain/range checker, not a new
    // escape hatch). Differing-arity overloads of the same name need no
    // check against each other (arity alone already makes them disjoint).
    results.extend(check_overload_disjointness(&fn_env, &name_defs, timeout_ms));

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
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    if timeout_ms > 0 {
        solver.set_option("tlimit", &timeout_ms.to_string());
    }

    let distinct_preds = build_distinct_preds(&tm, name_defs);
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
    let mut overload_obligs: Vec<self::encode::OverloadCallObligation<'_>> = Vec::new();
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

/// Verify that every `+` (disjoint union) in `set_expr` has genuinely disjoint operands.
///
/// Returns `Some(CheckResult)` on failure or `None` if all `+` nodes are proved disjoint.
/// Uses a fresh SMT solver per `+` node to avoid polluting the main check's solver state.
///
/// TODO: also validate `+` that appears inside function bodies (e.g. in `in` expressions).
fn validate_disjoint_unions(
    set_expr: &SemExpr,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Option<CheckResult> {
    use crate::semantics::tree::SemExprKind;
    match &set_expr.kind {
        SemExprKind::DisjointUnion(lhs, rhs) => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) {
                return Some(err);
            }
            if let Some(err) = validate_disjoint_unions(rhs, name_defs, timeout_ms) {
                return Some(err);
            }

            let tm = TermManager::new();
            let mut solver = Solver::new(&tm);
            solver.set_logic("ALL");
            if timeout_ms > 0 {
                solver.set_option("tlimit", &timeout_ms.to_string());
            }
            let distinct_preds = build_distinct_preds(&tm, name_defs);
            let t = tm.mk_const(tm.integer_sort(), "__disjoint_check");
            let in_a = membership_constraint(&tm, t.clone(), lhs, name_defs, &distinct_preds);
            let in_b = membership_constraint(&tm, t, rhs, name_defs, &distinct_preds);

            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => {
                    Some(CheckResult::Unknown(format!(
                        "cannot verify disjointness of `{lhs}` and `{rhs}`"
                    )))
                }
                (ca, cb) => {
                    if let Membership::Constrained(c) = ca {
                        solver.assert_formula(c);
                    }
                    if let Membership::Constrained(c) = cb {
                        solver.assert_formula(c);
                    }
                    let sat = solver.check_sat();
                    if sat.is_unsat() {
                        None // proved disjoint
                    } else if sat.is_sat() {
                        Some(CheckResult::Counterexample {
                            params: HashMap::new(),
                            output: 0,
                            reason: format!(
                                "`{lhs}` and `{rhs}` are not disjoint \
                                 — `+` requires disjoint sets; use `|` for plain union"
                            ),
                        })
                    } else {
                        Some(CheckResult::Unknown(format!(
                            "cannot prove `{lhs}` and `{rhs}` are disjoint"
                        )))
                    }
                }
            }
        }
        SemExprKind::SetDifference(lhs, rhs)
        | SemExprKind::CartesianProduct(lhs, rhs)
        | SemExprKind::SetQuotient(lhs, rhs)
        | SemExprKind::BinOp { lhs, rhs, .. } => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) {
                return Some(err);
            }
            validate_disjoint_unions(rhs, name_defs, timeout_ms)
        }
        SemExprKind::Call { args, .. } => {
            for arg in args {
                if let Some(err) = validate_disjoint_unions(arg, name_defs, timeout_ms) {
                    return Some(err);
                }
            }
            None
        }
        SemExprKind::KleeneStar(inner) => validate_disjoint_unions(inner, name_defs, timeout_ms),
        _ => None,
    }
}

// ── Overload disjointness (int-soundness-plan phase 2) ───────────────────────

/// Fresh per-parameter-position solver constants for one overload group —
/// shared across every candidate in the group so their domain terms can be
/// asserted together and checked for a common witness. Every member of a
/// same-name-same-arity group is guaranteed to agree on `param_kinds`
/// (enforced by `elaborate::check_overload_kind_agreement`), so it's safe to
/// derive these once from any one member.
///
/// TODO: only scalar (`Int`/`Bool`) parameter positions are supported — a
/// `Tuple`/`TaggedUnion`/`Vector` position returns `Err` (reported as
/// `Unknown`), matching `validate_disjoint_unions`'s existing scalar-only
/// scope. Lift together if ever needed.
fn fresh_overload_param_terms<'tm>(
    param_kinds: &[ValKind],
    tm: &'tm TermManager,
) -> Result<Vec<Term<'tm>>, String> {
    param_kinds
        .iter()
        .enumerate()
        .map(|(i, kind)| match kind {
            ValKind::Bool => Ok(tm.mk_const(tm.boolean_sort(), &format!("__ov_disjoint_{i}"))),
            ValKind::Int => Ok(tm.mk_const(tm.integer_sort(), &format!("__ov_disjoint_{i}"))),
            _ => Err(
                "cannot verify overload disjointness: non-scalar parameter positions \
                 are not yet supported"
                    .to_string(),
            ),
        })
        .collect()
}

/// The term "`param_terms` lie in `def`'s declared domain" — an OR across
/// `def`'s own signatures (one overload may itself declare more than one
/// signature over one shared body, exactly like today's non-overloaded
/// functions) of an AND across parameter positions.
fn overload_domain_term<'tm>(
    def: &SemFunctionDef,
    param_terms: &[Term<'tm>],
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &DistinctPreds<'tm>,
) -> Result<Term<'tm>, String> {
    let mut arms: Vec<Term<'_>> = Vec::new();
    for sig in &def.sigs {
        let parts = sem_param_set_exprs(sig.domain.as_ref(), param_terms.len()).map_err(|_| {
            format!(
                "cannot verify overload disjointness for `{}`: signature arity mismatch \
                 (internal error)",
                def.name.0
            )
        })?;
        let mut conjuncts: Vec<Term<'_>> = Vec::new();
        for ((term, part), kind) in param_terms.iter().zip(&parts).zip(&def.param_kinds) {
            if *kind == ValKind::Bool {
                continue; // membership is definitional, no constraint needed
            }
            match membership_constraint(tm, term.clone(), part, name_defs, distinct_preds) {
                Membership::Unconstrained => {}
                Membership::Constrained(c) => conjuncts.push(c),
                Membership::Unsupported => {
                    return Err(format!(
                        "cannot verify overload disjointness for `{}`: domain `{}` uses syntax \
                         not yet supported in the SMT encoding",
                        def.name.0, part
                    ));
                }
            }
        }
        arms.push(match conjuncts.len() {
            0 => tm.mk_boolean(true),
            1 => conjuncts.into_iter().next().unwrap(),
            _ => tm.mk_term(Kind::And, &conjuncts),
        });
    }
    Ok(match arms.len() {
        1 => arms.into_iter().next().unwrap(),
        _ => tm.mk_term(Kind::Or, &arms),
    })
}

/// Prove `def_a`'s and `def_b`'s declared domains share no value — a
/// counterexample is a witness argument tuple in both.
fn check_pair_disjoint(
    def_a: &SemFunctionDef,
    def_b: &SemFunctionDef,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> CheckResult {
    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_distinct_preds(&tm, name_defs);

    let param_terms = match fresh_overload_param_terms(&def_a.param_kinds, &tm) {
        Ok(v) => v,
        Err(e) => return CheckResult::Unknown(e),
    };
    let term_a = match overload_domain_term(def_a, &param_terms, &tm, name_defs, &distinct_preds) {
        Ok(t) => t,
        Err(e) => return CheckResult::Unknown(e),
    };
    let term_b = match overload_domain_term(def_b, &param_terms, &tm, name_defs, &distinct_preds) {
        Ok(t) => t,
        Err(e) => return CheckResult::Unknown(e),
    };
    solver.assert_formula(term_a);
    solver.assert_formula(term_b);

    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        let mut params = HashMap::new();
        for (i, term) in param_terms.iter().enumerate() {
            let val = solver.get_value(term.clone());
            let n = if term.sort().is_boolean() {
                boolean_value(&val) as i64
            } else {
                integer_value(&val)
            };
            params.insert(format!("arg{i}"), n);
        }
        CheckResult::Counterexample {
            params,
            output: 0,
            reason: format!(
                "overloads of `{}` are not disjoint — a value exists in both declared domains; \
                 overload domains must be disjoint (design-decisions.md §7)",
                def_a.name.0
            ),
        }
    } else {
        CheckResult::Unknown(format!(
            "cannot prove overloads of `{}` are disjoint",
            def_a.name.0
        ))
    }
}

/// Pairwise-disjointness obligations for every (name, arity) group with more
/// than one member in `fn_env` — groups of differing arity for the same
/// name need no check (arity alone is always statically decidable, so it
/// already makes them disjoint).
fn check_overload_disjointness(
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Vec<(String, Vec<(String, CheckResult)>)> {
    let mut out = Vec::new();
    for (name, defs) in fn_env {
        let mut by_arity: HashMap<usize, Vec<&SemFunctionDef>> = HashMap::new();
        for def in defs {
            by_arity.entry(def.params.len()).or_default().push(*def);
        }
        for group in by_arity.values() {
            if group.len() < 2 {
                continue;
            }
            let mut sig_results = Vec::new();
            for i in 0..group.len() {
                for j in (i + 1)..group.len() {
                    let label =
                        format!("{} (overload {} vs {}, disjointness)", name.0, i + 1, j + 1);
                    let result = check_pair_disjoint(group[i], group[j], name_defs, timeout_ms);
                    sig_results.push((label, result));
                }
            }
            out.push((name.0.clone(), sig_results));
        }
    }
    out
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
fn configured_solver<'tm>(tm: &'tm TermManager, timeout_ms: u64) -> Solver<'tm> {
    let mut solver = Solver::new(tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
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
    distinct_preds: &DistinctPreds<'tm>,
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
    distinct_preds: &DistinctPreds<'tm>,
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
    distinct_preds: &'a DistinctPreds<'tm>,
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
    let distinct_preds = build_distinct_preds(&tm, name_defs);

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
    let mut overload_obligs: Vec<self::encode::OverloadCallObligation<'_>> = Vec::new();
    let mut ssa_counter = 0usize;
    let mut constraint_env: HashMap<Symbol, SemExpr> = HashMap::new();
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
    decide_overflow_obligations(&overflow_obligs, &tm, &solver, channels.overflow_checks);
    self::encode::decide_overload_resolutions(
        &overload_obligs,
        &tm,
        &solver,
        channels.overload_resolutions,
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
    let distinct_preds = build_distinct_preds(&tm, name_defs);

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
    let mut overload_obligs: Vec<self::encode::OverloadCallObligation<'_>> = Vec::new();
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

    // See `check_block_sig`'s identical comment: must run before `finish_check`'s
    // negated-goal assertion.
    decide_overflow_obligations(&overflow_obligs, &tm, &solver, channels.overflow_checks);
    self::encode::decide_overload_resolutions(
        &overload_obligs,
        &tm,
        &solver,
        channels.overload_resolutions,
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
