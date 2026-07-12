//! Builders for the three cross-cutting "opaque identity" registries bundled
//! into `SolverPreds` (distinct sets, wrapping fixed-width integers, quotient
//! sets), plus the one-time quotient-set validation pass.
//!
//! Split out of `mod.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — mirrors phase 1's own
//! `encode.rs` → `encode_call.rs` split and phase 2's `expr.rs` →
//! `overload_dispatch.rs` split.

use std::collections::HashMap;

use cvc5::{Kind, TermManager};

use crate::{
    ast::DefKind,
    semantics::tree::{SemExpr, SemExprKind, SemFunctionBody, SemFunctionDef, SemItem},
    span::Symbol,
};

use super::membership::{
    CompCtx, DistinctInfo, DistinctPreds, Membership, QuotientInfo, QuotientPreds, SolverPreds,
    WrappingInfo, WrappingPreds, encode_comp_expr, membership_constraint,
};
use super::sort::set_sort;
use super::{CheckResult, FunctionEnv, NameDefs, configured_solver};

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
/// `Fail`, `None`, and `Char` are registered here too, as builtin distinct
/// sorts — none appears in `name_defs` (all three are resolved via
/// `builtins::lookup`, not a user definition), so they're added
/// unconditionally alongside the user-defined ones. This is the only
/// Fail/None-specific step in the whole cross-kind union pipeline: once each
/// has its own uninterpreted CVC5 sort, every other piece (cross-kind
/// detection in `set_sort`, datatype construction in
/// `build_union_datatype_sort`, membership, coercion) already treats any
/// distinct-sort arm generically, so `Int | Fail`, `Int | None`, and
/// `Int | (Fail * Y)` need no Fail/None-specific code beyond this
/// registration. See docs/design-decisions.md §4/§13.
///
/// `Char` reuses the exact same recipe, but — unlike `Fail`/`None` — its
/// constructor (`char(n)`, `solver::encode_call`) carries a genuine basis
/// obligation (not every `Int` is a valid Unicode scalar), so it's *not*
/// total the way `Fail`/`None`'s single witness value is.
pub(super) fn build_distinct_preds<'tm>(
    tm: &'tm TermManager,
    name_defs: &NameDefs,
) -> DistinctPreds<'tm> {
    let user_defined = name_defs
        .iter()
        .filter(|(_, def)| def.kind == DefKind::Distinct)
        .map(|(sym, _)| sym.clone());
    let with_builtins = user_defined.chain([
        Symbol::new("Fail"),
        Symbol::new("None"),
        Symbol::new("Char"),
    ]);

    with_builtins
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

/// Build the wrapping fixed-width integer registry (`Signed32`/`Unsigned32`,
/// docs/wrapping-and-quotient-sets-plan.md Feature 1): for each, a fresh
/// uninterpreted sort plus constructor/destructor uninterpreted functions
/// connecting straight to a native `(_ BitVec 32)` term — never `Int` — so
/// `+ - * neg` and comparisons between two same-family operands stay
/// entirely in bit-vector land (see `WrappingInfo`'s doc comment for why).
///
/// Unconditional and name-fixed (both builtins always exist, unlike
/// `distinct` sets which are only registered when the user actually declares
/// one) — no `name_defs` dependency, unlike `build_distinct_preds`.
pub(super) fn build_wrapping_preds(tm: &TermManager) -> WrappingPreds<'_> {
    [("Signed32", true), ("Unsigned32", false)]
        .into_iter()
        .map(|(name, signed)| {
            let width = 32;
            let bv_sort = tm.mk_bv_sort(width);
            let d_sort = tm.mk_uninterpreted_sort(name);
            let mk = tm.mk_const(
                tm.mk_fun_sort(std::slice::from_ref(&bv_sort), d_sort.clone()),
                &format!("mk_{name}"),
            );
            let from = tm.mk_const(
                tm.mk_fun_sort(std::slice::from_ref(&d_sort), bv_sort),
                &format!("from_{name}"),
            );
            (
                Symbol::new(name),
                WrappingInfo {
                    width,
                    signed,
                    d_sort,
                    mk,
                    from,
                },
            )
        })
        .collect()
}

/// Build the full `SolverPreds` bundle for one solver instance: distinct
/// sets, wrapping fixed-width integer sorts, and quotient sets, in that
/// dependency order — `build_quotient_preds` calls `set_sort`, which needs
/// the other two registries already built, but doesn't need its *own*
/// (still-being-built) output, so it's safe to hand it a `SolverPreds` with
/// an empty `quotient` map and fill that field in afterwards via struct-
/// update syntax (no cloning of `distinct`/`wrapping` needed).
pub(super) fn build_solver_preds<'tm>(
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    fn_env: &FunctionEnv<'_>,
) -> SolverPreds<'tm> {
    let sort_lookup = SolverPreds {
        distinct: build_distinct_preds(tm, name_defs),
        wrapping: build_wrapping_preds(tm),
        quotient: QuotientPreds::new(),
    };
    let quotient = build_quotient_preds(tm, name_defs, fn_env, &sort_lookup);
    SolverPreds {
        quotient,
        ..sort_lookup
    }
}

/// Resolve a quotient set's canonicalizer `Symbol` against `fn_env`: it must
/// be exactly one (non-overloaded) function, taking exactly one parameter,
/// with a single-expression body — a block body would need real statement
/// encoding, which this slice's `encode_comp_expr`-based approach doesn't
/// support (see `build_quotient_preds`'s own doc comment). Returns `None`
/// (rather than erring) for any shape this doesn't recognize; the
/// authoritative diagnostic for *why* a given quotient definition doesn't
/// qualify is `validate_quotient_sets`'s job, run once before the main
/// per-function loop — this is just the best-effort registration re-run
/// fresh for every solver instance (see `build_quotient_preds`).
fn resolve_canonicalizer<'a>(
    canon_sym: &Symbol,
    fn_env: &FunctionEnv<'a>,
) -> Option<(&'a Symbol, &'a SemExpr)> {
    let defs = fn_env.get(canon_sym)?;
    // See `check_quotient_def`'s identical tolerance: int64_split's phase 3
    // step 4a may have already split a single user-declared canonicalizer
    // into a compiler-generated `Int64`/`BigInt` pair sharing one body.
    if defs.len() > 1 && !defs.iter().all(|d| d.compiler_generated_split) {
        return None;
    }
    let def = defs.first().copied()?;
    if def.params.len() != 1 {
        return None;
    }
    match &def.body {
        SemFunctionBody::Expr(body) => Some((&def.params[0].name, body)),
        SemFunctionBody::Block(_) => None,
    }
}

/// Build the quotient-set registry (`L / canon`, docs/wrapping-and-quotient-
/// sets-plan.md's Feature 2): for every top-level `NameDef` whose value is a
/// `SetQuotient`, resolves the canonicalizer against `fn_env` and records its
/// sort/param/body — see `QuotientInfo`'s doc comment for why this stores
/// raw ingredients rather than a precomputed axiom (an earlier version
/// asserted `∀x. canon(x) == body(x)` onto every per-signature solver
/// unconditionally, which was observed to make cvc5 hang on files
/// containing an unrelated function; `membership_constraint`'s `SetQuotient`
/// arm encodes the body on demand instead, no quantifier involved).
///
/// This is re-run fresh for *every* solver instance (`check_name_def`/
/// `check_sig`/`check_block_sig` each get their own `TermManager`), but it
/// does *not* re-prove idempotence or domain/range containment each time —
/// `validate_quotient_sets` proves those exactly once, before the main
/// per-function loop, and gates `all_proved` in `check_file` on its own;
/// this function trusts that result and just re-registers the
/// (elsewhere-validated) canonicalizer. One that doesn't resolve cleanly is
/// silently skipped here — `validate_quotient_sets` is the authoritative
/// place that reports it as a compile error, so a membership check reaching
/// an unregistered quotient here ends up `Unsupported` → `Unknown`, never a
/// wrong answer.
fn build_quotient_preds<'tm>(
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    fn_env: &FunctionEnv<'_>,
    distinct_preds: &SolverPreds<'tm>,
) -> QuotientPreds<'tm> {
    let mut out = QuotientPreds::new();
    for def in name_defs.values() {
        let SemExprKind::SetQuotient(lhs, canon_sym) = &def.value.kind else {
            continue;
        };
        if out.contains_key(canon_sym) {
            continue;
        }
        let Some((param_sym, body)) = resolve_canonicalizer(canon_sym, fn_env) else {
            continue;
        };
        let Some(sort) = set_sort(tm, lhs, distinct_preds, name_defs) else {
            continue;
        };
        out.insert(
            canon_sym.clone(),
            QuotientInfo {
                sort,
                param: param_sym.clone(),
                body: body.clone(),
            },
        );
    }
    out
}

/// One-time validation for every quotient-set definition in the file — run
/// once before the main per-function loop (mirrors `check_overload_disjointness`'s
/// placement and shape: extends `results`, gating `all_proved` the same way).
/// Proves what `build_quotient_preds` only *assumes* on every later,
/// per-signature solver instance: that the canonicalizer resolves to a
/// genuine one-argument, single-expression, non-overloaded function; that
/// its declared range is provably `⊆ L` (the quotient's own basis set,
/// standard graduated domain/range containment — reuses
/// `membership_constraint`, no new proof kind); and idempotence (`∀x∈L.
/// f(f(x)) == f(x)`) — the one genuinely new proof kind this feature
/// introduces. Per fork 3 of docs/wrapping-and-quotient-sets-plan.md, an
/// unproved idempotence claim has no runtime fallback (it's a claim about
/// every element of a possibly-infinite set, not a single call-site value),
/// so — like disjointness and every other entry in `results` — it simply
/// gates `all_proved`; there is no `assume` escape hatch for it.
pub(super) fn validate_quotient_sets(
    name_defs: &NameDefs,
    fn_env: &FunctionEnv<'_>,
    timeout_ms: u64,
) -> Vec<(String, Vec<(String, CheckResult)>)> {
    name_defs
        .iter()
        .filter_map(|(name, def)| {
            let SemExprKind::SetQuotient(lhs, canon_sym) = &def.value.kind else {
                return None;
            };
            let label = format!("{name} = {lhs} / {canon_sym} (quotient set)");
            let result = check_quotient_def(lhs, canon_sym, name_defs, fn_env, timeout_ms);
            Some((name.0.clone(), vec![(label, result)]))
        })
        .collect()
}

fn check_quotient_def(
    lhs: &SemExpr,
    canon_sym: &Symbol,
    name_defs: &NameDefs,
    fn_env: &FunctionEnv<'_>,
    timeout_ms: u64,
) -> CheckResult {
    let Some(defs) = fn_env.get(canon_sym) else {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}` is not a defined function"
        ));
    };
    // int-soundness-plan phase 3 step 4a may already have split a single
    // user-declared `Int -> Int` canonicalizer into a compiler-generated
    // `Int64`/`BigInt` overload *pair* by this point (`check_file` runs
    // `int64_split` before building `fn_env`) — that's not a genuine user
    // overload, so tolerate it here, but a real user overload of the same
    // name is still rejected.
    if defs.len() > 1 && !defs.iter().all(|d| d.compiler_generated_split) {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}` must not be an overloaded name"
        ));
    }
    let Some(def) = defs.first().copied() else {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}` is not a defined function"
        ));
    };
    if def.params.len() != 1 {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}` must take exactly one parameter, got {}",
            def.params.len()
        ));
    }
    let SemFunctionBody::Expr(body) = &def.body else {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}` must have a single-expression body \
             (block bodies not yet supported for quotient-set canonicalizers)"
        ));
    };
    let param_sym = &def.params[0].name;
    // Every def in a compiler-generated split has exactly one (narrowed)
    // signature; check *each* def's range separately below — together they
    // cover the same ground as the original, pre-split `Int -> Int`
    // signature would have.
    for other in defs {
        if other.sigs.len() != 1 {
            return CheckResult::Unknown(format!(
                "canonicalizer `{canon_sym}` must have exactly one signature"
            ));
        }
    }

    let tm = TermManager::new();
    let distinct_preds = SolverPreds {
        // No `fn_env`-derived quotient axioms here: a canonicalizer body
        // referencing another quotient set's membership is out of scope
        // for this slice (see `build_quotient_preds`'s doc comment).
        distinct: build_distinct_preds(&tm, name_defs),
        wrapping: build_wrapping_preds(&tm),
        quotient: QuotientPreds::new(),
    };
    let Some(sort) = set_sort(&tm, lhs, &distinct_preds, name_defs) else {
        return CheckResult::Unknown(format!(
            "quotient set's basis `{lhs}` has no representable solver sort"
        ));
    };

    // 1. Range containment: f's declared range must be `⊆ L` — same
    // "prove part ⊆ whole" shape as `int64_split::domain_within_int64`.
    // Checked for *every* def in `defs` (usually just one; two when
    // compiler-split — their ranges union back to the original range, so
    // proving each separately proves the original signature's containment).
    for other in defs {
        let range = &other.sigs[0].range;
        let mut solver = configured_solver(&tm, timeout_ms);
        let t = tm.mk_const(sort.clone(), "__quotient_range_check");
        let in_range = membership_constraint(&tm, t.clone(), range, name_defs, &distinct_preds);
        let in_lhs = membership_constraint(&tm, t, lhs, name_defs, &distinct_preds);
        if matches!(in_range, Membership::Unsupported) || matches!(in_lhs, Membership::Unsupported)
        {
            return CheckResult::Unknown(format!(
                "cannot verify that canonicalizer `{canon_sym}`'s range `{range}` is a subset of `{lhs}`"
            ));
        }
        if let Membership::Constrained(c) = in_range {
            solver.assert_formula(c);
        }
        match in_lhs {
            // `lhs` imposes no constraint at all — everything is trivially
            // in `lhs`, so `range ⊆ lhs` holds unconditionally: force unsat
            // (mirrors `domain_within_int64`'s identical case).
            Membership::Unconstrained => solver.assert_formula(tm.mk_boolean(false)),
            Membership::Constrained(c) => {
                solver.assert_formula(tm.mk_term(Kind::Not, &[c]));
            }
            Membership::Unsupported => unreachable!("handled above"),
        }
        if !solver.check_sat().is_unsat() {
            return CheckResult::Counterexample {
                params: HashMap::new(),
                output: 0,
                reason: format!(
                    "canonicalizer `{canon_sym}`'s range `{range}` is not provably a subset of `{lhs}`"
                ),
            };
        }
    }

    // 2. Idempotence: ∀x∈L. f(f(x)) == f(x) — encoded as a universally-
    // quantified goal (same `Kind::Forall` shape as sequence-membership
    // `∀i` goals), proved by refuting its negation.
    let mut solver = configured_solver(&tm, timeout_ms);
    let x = tm.mk_var(sort.clone(), "x");
    let comp_ctx = CompCtx {
        tm: &tm,
        name_defs,
        distinct_preds: &distinct_preds,
    };
    let Some(f_x) = encode_comp_expr(body, param_sym, x.clone(), comp_ctx) else {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}`'s body uses syntax not yet supported \
             for quotient-set idempotence checking"
        ));
    };
    let Some(f_f_x) = encode_comp_expr(body, param_sym, f_x.clone(), comp_ctx) else {
        return CheckResult::Unknown(format!(
            "canonicalizer `{canon_sym}`'s body uses syntax not yet supported \
             for quotient-set idempotence checking"
        ));
    };
    let in_lhs = membership_constraint(&tm, x.clone(), lhs, name_defs, &distinct_preds);
    if matches!(in_lhs, Membership::Unsupported) {
        return CheckResult::Unknown(format!(
            "cannot verify idempotence: `{lhs}` has unsupported membership syntax"
        ));
    }
    // Prove `∀x∈L. f(f(x)) == f(x)` by refuting `∃x∈L. f(f(x)) != f(x)` —
    // `x` is a bound (`mk_var`) term, so the negated goal must itself be
    // properly quantified (an `Exists` wrapping the free `x`), not asserted
    // as a bare formula with `x` left free.
    let neq = tm.mk_term(Kind::Distinct, &[f_f_x, f_x]);
    let counterexample_body = match in_lhs {
        Membership::Unconstrained => neq,
        Membership::Constrained(guard) => tm.mk_term(Kind::And, &[guard, neq]),
        Membership::Unsupported => unreachable!("handled above"),
    };
    let vars = tm.mk_term(Kind::VariableList, &[x]);
    solver.assert_formula(tm.mk_term(Kind::Exists, &[vars, counterexample_body]));
    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: format!(
                "canonicalizer `{canon_sym}` is not idempotent: found x ∈ `{lhs}` with \
                 `{canon_sym}({canon_sym}(x)) != {canon_sym}(x)`"
            ),
        }
    } else {
        CheckResult::Unknown(format!(
            "could not prove canonicalizer `{canon_sym}` is idempotent"
        ))
    }
}

// ── Function equivalence checking (`equiv f, g`) ────────────────────────────
//
// A new kind of compile-time claim, not covered by ordinary domain/range
// checking: two *different*, already-defined functions agree on their
// shared domain. Reuses `encode_comp_expr` (the same single-parameter,
// single-expression-body encoder quotient-set canonicalizers use) rather
// than the full `encode_expr`/`EncodeCtx` machinery — same v0 restriction
// (no calls, no if/else, no block bodies) as quotient sets accepted for
// exactly the same reason: it's the smallest slice that's still genuinely
// useful, and it introduces zero new `Kind`/codegen surface area. Lifting
// the restriction to arbitrary function bodies is real, separate future
// work, not attempted here.

/// Resolve `name` to its single definition, tolerating int-soundness-plan
/// phase 3's compiler-generated `Int64`/`BigInt` split pair exactly like
/// `check_quotient_def` does for canonicalizers above — a genuine user
/// overload of the same name is still rejected, since `equiv` compares one
/// concrete function, not a whole overload set.
fn single_def<'a>(name: &Symbol, fn_env: &FunctionEnv<'a>) -> Result<&'a SemFunctionDef, String> {
    let defs = fn_env
        .get(name)
        .ok_or_else(|| format!("`{name}` is not a defined function"))?;
    if defs.len() > 1 && !defs.iter().all(|d| d.compiler_generated_split) {
        return Err(format!("`{name}` must not be an overloaded name"));
    }
    defs.first()
        .copied()
        .ok_or_else(|| format!("`{name}` is not a defined function"))
}

pub(super) fn validate_equiv_decls(
    sem_items: &[SemItem],
    name_defs: &NameDefs,
    fn_env: &FunctionEnv<'_>,
    timeout_ms: u64,
) -> Vec<(String, Vec<(String, CheckResult)>)> {
    sem_items
        .iter()
        .filter_map(|item| {
            let SemItem::EquivDecl { lhs, rhs, .. } = item else {
                return None;
            };
            let label = format!("equiv {lhs}, {rhs}");
            let result = check_equiv_decl(lhs, rhs, name_defs, fn_env, timeout_ms);
            // Reuses `lhs`'s own name as the grouping key — the same trick
            // `check_overload_disjointness`'s synthetic entries already rely
            // on (see main.rs's `items_by_name`/`next_item_idx`): once a
            // name's *real* signature results are exhausted, extra entries
            // under the same key correctly fall back to displaying `label`
            // verbatim instead of being matched against a real signature.
            Some((lhs.0.clone(), vec![(label, result)]))
        })
        .collect()
}

fn check_equiv_decl(
    lhs: &Symbol,
    rhs: &Symbol,
    name_defs: &NameDefs,
    fn_env: &FunctionEnv<'_>,
    timeout_ms: u64,
) -> CheckResult {
    let lhs_def = match single_def(lhs, fn_env) {
        Ok(d) => d,
        Err(msg) => return CheckResult::Unknown(msg),
    };
    let rhs_def = match single_def(rhs, fn_env) {
        Ok(d) => d,
        Err(msg) => return CheckResult::Unknown(msg),
    };

    if lhs_def.params.len() != 1 || rhs_def.params.len() != 1 {
        return CheckResult::Unknown(format!(
            "`equiv` currently only supports single-parameter functions \
             (`{lhs}` has {}, `{rhs}` has {})",
            lhs_def.params.len(),
            rhs_def.params.len()
        ));
    }
    if lhs_def.sigs.len() != 1 || rhs_def.sigs.len() != 1 {
        return CheckResult::Unknown(
            "`equiv` currently only supports functions with exactly one signature".to_string(),
        );
    }
    let SemFunctionBody::Expr(lhs_body) = &lhs_def.body else {
        return CheckResult::Unknown(format!(
            "`{lhs}` must have a single-expression body (block bodies not yet \
             supported for `equiv`)"
        ));
    };
    let SemFunctionBody::Expr(rhs_body) = &rhs_def.body else {
        return CheckResult::Unknown(format!(
            "`{rhs}` must have a single-expression body (block bodies not yet \
             supported for `equiv`)"
        ));
    };
    let Some(lhs_domain) = lhs_def.sigs[0].domain.as_ref() else {
        return CheckResult::Unknown(format!("`{lhs}` has no domain to quantify over"));
    };
    let Some(rhs_domain) = rhs_def.sigs[0].domain.as_ref() else {
        return CheckResult::Unknown(format!("`{rhs}` has no domain to quantify over"));
    };

    let tm = TermManager::new();
    let distinct_preds = SolverPreds {
        distinct: build_distinct_preds(&tm, name_defs),
        wrapping: build_wrapping_preds(&tm),
        quotient: QuotientPreds::new(),
    };

    let Some(sort) = set_sort(&tm, lhs_domain, &distinct_preds, name_defs) else {
        return CheckResult::Unknown(format!("`{lhs}`'s domain has no representable solver sort"));
    };
    let Some(rhs_sort) = set_sort(&tm, rhs_domain, &distinct_preds, name_defs) else {
        return CheckResult::Unknown(format!("`{rhs}`'s domain has no representable solver sort"));
    };
    if sort != rhs_sort {
        return CheckResult::Unknown(format!(
            "`{lhs}` and `{rhs}` take differently-represented parameters, cannot compare"
        ));
    }

    let mut solver = configured_solver(&tm, timeout_ms);
    let x = tm.mk_var(sort, "x");
    let comp_ctx = CompCtx {
        tm: &tm,
        name_defs,
        distinct_preds: &distinct_preds,
    };
    let lhs_param = &lhs_def.params[0].name;
    let rhs_param = &rhs_def.params[0].name;
    let Some(lhs_result) = encode_comp_expr(lhs_body, lhs_param, x.clone(), comp_ctx) else {
        return CheckResult::Unknown(format!(
            "`{lhs}`'s body uses syntax `equiv` doesn't support yet \
             (only arithmetic/comparisons — no calls, if/else, or block bodies)"
        ));
    };
    let Some(rhs_result) = encode_comp_expr(rhs_body, rhs_param, x.clone(), comp_ctx) else {
        return CheckResult::Unknown(format!(
            "`{rhs}`'s body uses syntax `equiv` doesn't support yet \
             (only arithmetic/comparisons — no calls, if/else, or block bodies)"
        ));
    };
    if lhs_result.sort() != rhs_result.sort() {
        return CheckResult::Unknown(format!(
            "`{lhs}` and `{rhs}` return differently-represented values, cannot compare"
        ));
    }

    // Quantify over the *shared* domain, not either function's full
    // declared domain in isolation — calling `rhs` outside its own checked
    // domain (or vice versa) gives no guarantee to compare against, so
    // restricting the search to `dom(lhs) ∩ dom(rhs)` is both the safe and
    // the mathematically natural framing (and costs nothing extra: it's the
    // same conjunction-of-two-membership-constraints shape already used for
    // range containment above). A shared domain that's provably empty makes
    // the claim vacuously (and correctly) `Proved` — no witness was ever
    // searched for, which is the right answer, just worth knowing about.
    let in_lhs_dom = membership_constraint(&tm, x.clone(), lhs_domain, name_defs, &distinct_preds);
    let in_rhs_dom = membership_constraint(&tm, x.clone(), rhs_domain, name_defs, &distinct_preds);
    if matches!(in_lhs_dom, Membership::Unsupported)
        || matches!(in_rhs_dom, Membership::Unsupported)
    {
        return CheckResult::Unknown(format!(
            "cannot verify `{lhs}`/`{rhs}`'s shared domain — unsupported membership syntax"
        ));
    }
    let shared_domain_guard = match (in_lhs_dom, in_rhs_dom) {
        (Membership::Unconstrained, Membership::Unconstrained) => None,
        (Membership::Unconstrained, Membership::Constrained(c))
        | (Membership::Constrained(c), Membership::Unconstrained) => Some(c),
        (Membership::Constrained(a), Membership::Constrained(b)) => {
            Some(tm.mk_term(Kind::And, &[a, b]))
        }
        (Membership::Unsupported, _) | (_, Membership::Unsupported) => {
            unreachable!("handled above")
        }
    };

    // Prove `∀x ∈ dom(lhs) ∩ dom(rhs). lhs(x) == rhs(x)` by refuting
    // `∃x ∈ (shared domain). lhs(x) != rhs(x)` — same shape as
    // `check_quotient_def`'s idempotence proof above.
    let neq = tm.mk_term(Kind::Distinct, &[lhs_result, rhs_result]);
    let counterexample_body = match shared_domain_guard {
        None => neq,
        Some(guard) => tm.mk_term(Kind::And, &[guard, neq]),
    };
    let vars = tm.mk_term(Kind::VariableList, &[x]);
    solver.assert_formula(tm.mk_term(Kind::Exists, &[vars, counterexample_body]));
    let sat = solver.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        CheckResult::Counterexample {
            params: HashMap::new(),
            output: 0,
            reason: format!(
                "found x in the shared domain of `{lhs}`/`{rhs}` where `{lhs}(x) != {rhs}(x)`"
            ),
        }
    } else {
        CheckResult::Unknown(format!(
            "could not prove `{lhs}` and `{rhs}` are equivalent"
        ))
    }
}
