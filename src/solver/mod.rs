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

use cvc5::{Kind, Solver, Term, TermManager};

use crate::{
    ast::{DefKind, Item},
    semantics::{
        elaborate::elaborate,
        tree::{sem_param_set_exprs, SemExpr, SemFunctionBody, SemFunctionDef, SemFunctionSig, SemItem, SemNameDef},
    },
    span::{Span, Symbol},
};

/// Map from name to its elaborated `SemNameDef` — built once per `check_file`
/// call from `elaborate()`'s output. Unlike codegen, the solver needs the
/// full elaborated value (not just `Kind`) for expanding aliases and
/// evaluating annotated constants during encoding.
pub(crate) type NameDefs = HashMap<Symbol, SemNameDef>;

use crate::kind::Kind as ValKind;

use self::encode::{Env, BuiltinObligation, OverflowObligation, decide_overflow_obligations, encode_expr, integer_value, boolean_value, mk_decomposed_tuple};
use self::sort::set_sort;
use self::blocks::{encode_block, body_has_unconstrained_loop_var};
use self::membership::{DistinctInfo, DistinctPreds, Membership, membership_constraint};

// ── Public types ──────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
pub enum CheckResult {
    /// Every input satisfying the domain maps to an output in the range,
    /// and no built-in operation can produce undefined behaviour.
    Proved,
    /// The solver found concrete parameter values that violate a safety
    /// obligation.  `reason` is a human-readable explanation such as
    /// `"not in Nat"` (range violation) or `"division by zero"`.
    Counterexample { params: HashMap<String, i64>, output: i64, reason: String },
    /// Could not determine (unsupported construct, solver timeout, etc.).
    Unknown(String),
}

type FunctionEnv<'a> = HashMap<Symbol, &'a SemFunctionDef>;

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
    let user_defined = name_defs.iter()
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
                tm.mk_fun_sort(&[sort.clone()], tm.integer_sort()),
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
pub fn check_file(items: &[Item], timeout_ms: u64) -> Result<CheckOutcome, crate::error::CompileError> {
    let sem_items = elaborate(items)?;

    let fn_env: FunctionEnv<'_> = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::FunctionDef(def) => Some((def.name.clone(), def)),
            _ => None,
        })
        .collect();

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

    let results: Vec<(String, Vec<(String, CheckResult)>)> = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::FunctionDef(def) => {
                let results = check_function(def, &fn_env, &name_defs, timeout_ms, &mut overflow_checks);
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

    let all_proved = results
        .iter()
        .all(|(_, sig_results)| sig_results.iter().all(|(_, r)| *r == CheckResult::Proved));

    if all_proved {
        Ok(CheckOutcome::Proved(ConstrainedTree { items: items.to_vec(), sem_items, results, overflow_checks }))
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
) -> Result<Vec<(String, CheckResult)>, crate::error::CompileError> {
    let param_names: Vec<Symbol> = def.params.iter().map(|p| p.name.clone()).collect();

    Ok(def
        .sigs
        .iter()
        .enumerate()
        .map(|(i, sig)| {
            let label = sig_label(&def.name.0, i, def.sigs.len());
            let result = match &def.body {
                SemFunctionBody::Expr(body) => check_sig(sig, &param_names, body, fn_env, name_defs, timeout_ms, overflow_checks),
                SemFunctionBody::Block(stmts) => check_block_sig(sig, &param_names, stmts, fn_env, name_defs, timeout_ms, overflow_checks),
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

fn check_name_def(def: &SemNameDef, ty: &SemExpr, fn_env: &FunctionEnv<'_>, name_defs: &NameDefs, timeout_ms: u64) -> CheckResult {
    if let Some(result) = validate_disjoint_unions(ty, name_defs, timeout_ms) { return result; }
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }

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
    let top_guard = tm.mk_boolean(true);

    let value_term = match encode_expr(
        &def.value, &env, name_defs, fn_env, &tm, &mut solver,
        &mut call_counter, &mut builtin_obligs, &mut overflow_obligs, top_guard, &distinct_preds, None,
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    let range_obligation = match membership_constraint(&tm, value_term, ty, name_defs, &distinct_preds) {
        Membership::Unconstrained => None,
        Membership::Constrained(c) => Some(c),
        Membership::Unsupported => return CheckResult::Unknown("unsupported set annotation".into()),
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
fn validate_disjoint_unions(set_expr: &SemExpr, name_defs: &NameDefs, timeout_ms: u64) -> Option<CheckResult> {
    use crate::semantics::tree::SemExprKind;
    match &set_expr.kind {
        SemExprKind::DisjointUnion(lhs, rhs) => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) { return Some(err); }
            if let Some(err) = validate_disjoint_unions(rhs, name_defs, timeout_ms) { return Some(err); }

            let tm = TermManager::new();
            let mut solver = Solver::new(&tm);
            solver.set_logic("ALL");
            if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }
            let distinct_preds = build_distinct_preds(&tm, name_defs);
            let t = tm.mk_const(tm.integer_sort(), "__disjoint_check");
            let in_a = membership_constraint(&tm, t.clone(), lhs, name_defs, &distinct_preds);
            let in_b = membership_constraint(&tm, t, rhs, name_defs, &distinct_preds);

            match (in_a, in_b) {
                (Membership::Unsupported, _) | (_, Membership::Unsupported) => Some(
                    CheckResult::Unknown(format!("cannot verify disjointness of `{lhs}` and `{rhs}`"))
                ),
                (ca, cb) => {
                    if let Membership::Constrained(c) = ca { solver.assert_formula(c); }
                    if let Membership::Constrained(c) = cb { solver.assert_formula(c); }
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
        SemExprKind::SetDifference(lhs, rhs) | SemExprKind::CartesianProduct(lhs, rhs)
        | SemExprKind::SetQuotient(lhs, rhs) | SemExprKind::BinOp { lhs, rhs, .. } => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) { return Some(err); }
            validate_disjoint_unions(rhs, name_defs, timeout_ms)
        }
        SemExprKind::Call { args, .. } => {
            for arg in args {
                if let Some(err) = validate_disjoint_unions(arg, name_defs, timeout_ms) { return Some(err); }
            }
            None
        }
        SemExprKind::KleeneStar(inner) => validate_disjoint_unions(inner, name_defs, timeout_ms),
        _ => None,
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
fn configured_solver<'tm>(tm: &'tm TermManager, timeout_ms: u64) -> Solver<'tm> {
    let mut solver = Solver::new(tm);
    solver.set_logic("ALL");
    solver.set_option("produce-models", "true");
    // Sequence membership uses universally-quantified constraints (∀i. guard → elem∈X).
    // MBQI (model-based quantifier instantiation) finds concrete sequence witnesses
    // for existential goals arising from negated universals (counterexample direction).
    solver.set_option("mbqi", "true");
    if timeout_ms > 0 { solver.set_option("tlimit", &timeout_ms.to_string()); }
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
    let domain_parts: Vec<&SemExpr> = sem_param_set_exprs(domain, param_names.len())
        .map_err(CheckResult::Unknown)?;

    let mut param_terms: Vec<Term<'_>> = Vec::new();
    for (n, part) in param_names.iter().zip(domain_parts.iter()) {
        let k = part.kind_of.clone();
        if matches!(k, ValKind::Tuple(_)) {
            let (assembled, leaves) = mk_decomposed_tuple(tm, &n.0, part, distinct_preds, name_defs);
            for (leaf, leaf_set) in leaves {
                match membership_constraint(tm, leaf, leaf_set, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return Err(CheckResult::Unknown("unsupported domain set expression".into()));
                    }
                }
            }
            param_terms.push(assembled);
        } else {
            let sort = match set_sort(tm, part, distinct_preds, name_defs) {
                Some(s) => s,
                None => return Err(CheckResult::Unknown(format!(
                    "parameter `{}` has an unsupported domain sort (internal error)",
                    n.0
                ))),
            };
            let term = tm.mk_const(sort, &n.0);
            if k != ValKind::Bool {
                match membership_constraint(tm, term.clone(), part, name_defs, distinct_preds) {
                    Membership::Unconstrained => {}
                    Membership::Constrained(c) => solver.assert_formula(c),
                    Membership::Unsupported => {
                        return Err(CheckResult::Unknown("unsupported domain set expression".into()));
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
    for ((name, term), part) in param_names.iter().zip(param_terms.iter()).zip(domain_parts.iter()) {
        let val = solver.get_value(term.clone());
        let k = part.kind_of.clone();
        let n = if k == ValKind::Bool {
            boolean_value(&val) as i64
        } else if matches!(k, ValKind::Tuple(_)) {
            0 // TODO: render tuple model value in counterexample display
        } else if matches!(k, ValKind::TaggedUnion(_)) {
            0 // TODO: decode datatype arm for cross-kind union counterexample display
        } else if matches!(k, ValKind::Vector(_)) {
            0 // TODO: render vector model value in counterexample display
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

/// Shared tail of both signature checkers: combine the range obligation with
/// any built-in obligations, ask the solver to refute their conjunction, and
/// turn the result into a `CheckResult`. `extra_unknown_check` runs only on
/// the SAT (counterexample) path, before decoding witness params — it lets
/// `check_block_sig` report its loop-invariant-specific `Unknown` message
/// instead of a generic counterexample when that's the real cause.
#[allow(clippy::too_many_arguments)]
fn finish_check<'tm>(
    tm: &'tm TermManager,
    solver: &mut Solver<'tm>,
    body_term: Term<'tm>,
    range: &SemExpr,
    builtin_obligs: &[BuiltinObligation<'tm>],
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    domain_parts: &[&SemExpr],
    distinct_preds: &DistinctPreds<'tm>,
    name_defs: &NameDefs,
    extra_unknown_check: impl FnOnce() -> Option<CheckResult>,
) -> CheckResult {
    let range_obligation = match membership_constraint(tm, body_term.clone(), range, name_defs, distinct_preds) {
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
                tm.mk_term(Kind::Implies, &[o.path_cond.clone(), o.obligation.clone()])
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
        tm.mk_term(Kind::And, &all_obligations)
    };
    solver.assert_formula(tm.mk_term(Kind::Not, &[combined]));

    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        if let Some(early) = extra_unknown_check() {
            return early;
        }
        let cex_params = decode_cex_params(tm, solver, param_names, param_terms, domain_parts, distinct_preds);
        let reason = builtin_obligs
            .iter()
            .find(|o| {
                boolean_value(&solver.get_value(o.path_cond.clone()))
                    && !boolean_value(&solver.get_value(o.obligation.clone()))
            })
            .map(|o| o.violated_reason.to_string())
            .unwrap_or_else(|| format!("not in {}", range));
        let output_term = solver.get_value(body_term);
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

#[allow(clippy::too_many_arguments)]
fn check_block_sig(
    sig: &SemFunctionSig,
    param_names: &[Symbol],
    stmts: &[crate::semantics::tree::SemStmt],
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
    overflow_checks: &mut HashMap<Span, bool>,
) -> CheckResult {
    if let Some(dom) = &sig.domain {
        if let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms) { return result; }
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) { return result; }

    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_distinct_preds(&tm, name_defs);

    let (domain_parts, param_terms) = match build_param_terms(
        &tm, &mut solver, sig.domain.as_ref(), param_names, &distinct_preds, name_defs,
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
    let mut ssa_counter = 0usize;
    let mut constraint_env: HashMap<Symbol, SemExpr> = HashMap::new();
    let mut has_runtime_assert = false;
    let mut immutable_names: HashSet<Symbol> = HashSet::new();

    let result_sort = set_sort(&tm, &sig.range, &distinct_preds, &name_defs);
    let body_term = match encode_block(
        stmts,
        &mut env,
        name_defs,
        fn_env,
        &tm,
        &mut solver,
        &mut call_counter,
        &mut builtin_obligs,
        &mut overflow_obligs,
        &mut ssa_counter,
        param_names,
        &param_terms,
        &mut constraint_env,
        &mut has_runtime_assert,
        &mut immutable_names,
        &distinct_preds,
        overflow_checks,
        result_sort,
    ) {
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
    decide_overflow_obligations(&overflow_obligs, &tm, &solver, overflow_checks);

    if has_runtime_assert && !crate::semantics::tree::range_contains_fail(&sig.range) {
        return CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: "assert may fail at runtime but return type does not include `Fail` \
                     — add `| Fail` or use `!!` on the return type, or prove the assertion statically"
                .into(),
        };
    }

    finish_check(
        &tm, &mut solver, body_term, &sig.range, &builtin_obligs,
        param_names, &param_terms, &domain_parts, &distinct_preds, name_defs,
        || {
            body_has_unconstrained_loop_var(stmts, &constraint_env, &tm, name_defs, &distinct_preds).then(|| {
                CheckResult::Unknown(
                    "while loop: declare all mutable variable constraints \
                     (`mut name: Set = expr`) to enable counterexample extraction".into()
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
    overflow_checks: &mut HashMap<Span, bool>,
) -> CheckResult {
    if let Some(dom) = &sig.domain {
        if let Some(result) = validate_disjoint_unions(dom, name_defs, timeout_ms) { return result; }
    }
    if let Some(result) = validate_disjoint_unions(&sig.range, name_defs, timeout_ms) { return result; }

    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    let distinct_preds = build_distinct_preds(&tm, name_defs);

    let (domain_parts, param_terms) = match build_param_terms(
        &tm, &mut solver, sig.domain.as_ref(), param_names, &distinct_preds, name_defs,
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
    let top_guard = tm.mk_boolean(true);
    let body_term = match encode_expr(
        body, &env, name_defs, fn_env, &tm, &mut solver, &mut call_counter,
        &mut builtin_obligs, &mut overflow_obligs, top_guard, &distinct_preds, set_sort(&tm, &sig.range, &distinct_preds, &name_defs),
    ) {
        Ok(t) => t,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    // See `check_block_sig`'s identical comment: must run before `finish_check`'s
    // negated-goal assertion.
    decide_overflow_obligations(&overflow_obligs, &tm, &solver, overflow_checks);

    finish_check(
        &tm, &mut solver, body_term, &sig.range, &builtin_obligs,
        param_names, &param_terms, &domain_parts, &distinct_preds, name_defs,
        || None,
    )
}
