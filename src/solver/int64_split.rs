//! int-soundness-plan phase 3: two compiler-generated transforms that let a
//! function's params/return be represented as raw, untagged `Kind::Int64`
//! instead of the tagged `Kind::Int` step 4b introduces for every other
//! integer position.
//!
//! **Step A — whole-function promotion (`try_promote_to_int64`).** Most
//! existing Cantor functions already declare a domain that's a genuine
//! subset of `Int64` (`Int8`, `Int16`, `Int32`, a bounded custom set, …) —
//! for these there's no "otherwise" case a caller could ever hit (the
//! ordinary domain-membership proof obligation at every call site already
//! guarantees it), so the whole function can be promoted in place to
//! `Kind::Int64`, with no sibling overload and no runtime dispatch. This is
//! what keeps the overwhelming common case exactly as cheap as it is today
//! once step 4b starts tagging plain `Kind::Int` — see
//! docs/int-soundness-plan.md's "Tagging scope" discussion for why this
//! step exists at all (blanket tagging would otherwise tax every integer
//! operation in the language, not just genuinely-unbounded ones).
//!
//! **Step 4a — the `Int64`/`BigInt` overload split (`try_split`).** For a
//! function whose domain is *not* already bounded (the bare unbounded `Int`
//! builtin) but whose body still happens to stay within `Int64` for
//! whatever argument it's given, split it into two overloads: an `Int64`
//! fast path used when a call site can prove its argument fits, and a
//! `BigInt = Int - Int64` fallback. See below for this mechanism's own doc
//! comment.
//!
//! Both are **solver-gated, not unconditional** (corrected 2026-07-04 for
//! step 4a — see docs/int-soundness-plan.md's "The overload split" section
//! for the counterexample that ruled out an earlier unconditional design):
//! promotion/splitting only happens when the solver proves it's sound.
//!
//! **What "proves it's sound" requires, precisely.** It is *not* enough for
//! the outer `domain → range` contract alone to prove — two's-complement
//! `+`/`-`/`*`/`neg` are exact ring operations mod 2^64, so a chain of only
//! those is safe under raw wraparound hardware as long as the *final*
//! result is proved in range, but `/` breaks that argument: dividing an
//! intermediate value that already wrapped can produce a genuinely wrong
//! quotient even when the true final answer would have been in range. So
//! both mechanisms require every individual arithmetic node's own overflow
//! obligation (phase 1's per-node `Int64`-boundedness side channel) to also
//! prove `true` for the trial signature — see `trial_fully_proves_int64`.

use std::collections::HashMap;

use cvc5::{Kind as CvcKind, TermManager};

use crate::kind::Kind;
use crate::semantics::tree::{
    SemAssertElse, SemExpr, SemExprKind, SemFunctionBody, SemFunctionDef, SemFunctionSig, SemItem,
    SemStmt, sem_param_set_exprs,
};
use crate::span::{Span, Symbol};

use super::membership::{Membership, QuotientPreds, SolverPreds, membership_constraint};
use super::{
    CheckResult, FunctionEnv, NameDefs, build_distinct_preds, build_wrapping_preds, check_function,
    configured_solver,
};

/// Runs both transforms over every function in the file. Items that aren't
/// `FunctionDef`s, or don't qualify, or don't prove, pass through unchanged.
pub(super) fn generate_int64_bigint_splits(
    sem_items: Vec<SemItem>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Vec<SemItem> {
    // The real, file-wide contracts — used so a candidate body's calls to
    // any *other* function resolve against their genuine signatures during
    // the trial checks below. Only the candidate's own entry is overridden,
    // per candidate, inside `try_promote_to_int64`/`try_split`.
    let mut fn_env: FunctionEnv<'_> = FunctionEnv::new();
    for item in &sem_items {
        if let SemItem::FunctionDef(def) = item {
            fn_env.entry(def.name.clone()).or_default().push(def);
        }
    }

    let mut out = Vec::with_capacity(sem_items.len());
    for item in &sem_items {
        match item {
            // MVP scope for both transforms: only touch a name that has *no*
            // other FunctionDef in the file already — i.e. leave any
            // pre-existing user overload set (phase 2) entirely alone. This
            // isn't a fundamental limit, it just keeps this pass from also
            // having to reason about interactions with user-declared
            // overloading in this first cut.
            SemItem::FunctionDef(def) if fn_env.get(&def.name).is_some_and(|v| v.len() == 1) => {
                if let Some(promoted) = try_promote_to_int64(def, &fn_env, name_defs, timeout_ms) {
                    out.push(SemItem::FunctionDef(promoted));
                    continue;
                }
                match try_split(def, &fn_env, name_defs, timeout_ms) {
                    Some((int64_def, bigint_def)) => {
                        out.push(SemItem::FunctionDef(int64_def));
                        out.push(SemItem::FunctionDef(bigint_def));
                    }
                    None => out.push(item.clone()),
                }
            }
            SemItem::FunctionDef(_) | SemItem::NameDef(_) | SemItem::EquivDecl { .. } => {
                out.push(item.clone())
            }
        }
    }
    out
}

/// Run `check_function` for a trial signature and return `true` only if the
/// `domain → range` contract proves *and* every arithmetic node inside also
/// proves it stays within `Int64` — see this module's doc comment for why
/// the weaker "final result in range" check alone isn't sound once the body
/// can contain `/`. The trial's own `overflow_checks`/`overload_resolutions`
/// side-channel entries are scratch — thrown away either way, never merged
/// into the file's real maps (if the transform fires, the real per-function
/// loop in `check_file` checks the replacement item again from scratch and
/// populates those maps correctly then).
fn trial_fully_proves_int64<'a>(
    trial_def: &'a SemFunctionDef,
    trial_env: &FunctionEnv<'a>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> bool {
    let mut scratch_overflow = HashMap::new();
    let mut scratch_resolutions = HashMap::new();
    let Ok(results) = check_function(
        trial_def,
        trial_env,
        name_defs,
        timeout_ms,
        &mut scratch_overflow,
        &mut scratch_resolutions,
    ) else {
        return false;
    };
    let contract_proved = results.iter().all(|(_, r)| *r == CheckResult::Proved);
    contract_proved && scratch_overflow.values().all(|&proved| proved)
}

/// `true` iff the solver proves `part ⊆ Int64` (no witness value satisfies
/// `part` but not `Int64`). `false` on `Unknown`/unsupported syntax as well
/// as a genuine counterexample — this is an eligibility gate for an
/// optimization, not a proof obligation, so declining silently (leaving the
/// function as an ordinary `Kind::Int` body) is always the safe fallback.
fn domain_within_int64(part: &SemExpr, name_defs: &NameDefs, timeout_ms: u64) -> bool {
    let tm = TermManager::new();
    let mut solver = configured_solver(&tm, timeout_ms);
    // No `fn_env` available here — this is an eligibility check for an
    // optimization (whole-function Int64 promotion), not general membership
    // — so quotient-set membership safely degrades to `Unsupported` (i.e.
    // declines the optimization) rather than being threaded through.
    let distinct_preds = SolverPreds {
        distinct: build_distinct_preds(&tm, name_defs),
        wrapping: build_wrapping_preds(&tm),
        quotient: QuotientPreds::new(),
    };
    let t = tm.mk_const(tm.integer_sort(), "__int64_promote_check");
    let int64_expr = var_expr("Int64", Kind::Int64, part.span);

    let in_part = membership_constraint(&tm, t.clone(), part, name_defs, &distinct_preds);
    let in_int64 = membership_constraint(&tm, t, &int64_expr, name_defs, &distinct_preds);

    if matches!(in_part, Membership::Unsupported) || matches!(in_int64, Membership::Unsupported) {
        return false;
    }
    if let Membership::Constrained(c) = in_part {
        solver.assert_formula(c);
    }
    match in_int64 {
        // Int64 imposes no constraint at all (shouldn't happen for the real
        // Int64 builtin, but handled defensively): everything is trivially
        // in Int64, so `part ⊆ Int64` holds unconditionally — force unsat.
        Membership::Unconstrained => solver.assert_formula(tm.mk_boolean(false)),
        Membership::Constrained(c) => {
            let not_c = tm.mk_term(CvcKind::Not, &[c]);
            solver.assert_formula(not_c);
        }
        Membership::Unsupported => unreachable!("handled above"),
    }
    solver.check_sat().is_unsat()
}

/// Step A: promote a whole function to raw `Kind::Int64` in place, with no
/// sibling overload, when every parameter's declared domain component is
/// already provably `⊆ Int64` and the (unchanged) body proves sound under
/// `trial_fully_proves_int64`. Declines (returns `None`, leaving `def`
/// untouched) for anything not already scalar-`Int`-typed throughout —
/// `Bool`/`Tuple`/`Vector`/`TaggedUnion` positions never need this, and a
/// signature mixing `Int` with another Kind is a fast-follow, not this
/// first cut.
///
/// MVP eligibility, deliberately narrow like `try_split`: exactly one
/// signature, no pre-existing overload sibling (checked by the caller). No
/// restriction on arity or on `Mul` — unlike `try_split`, this doesn't
/// synthesize a *narrower* domain than what's already declared, so there's
/// no new nonlinear-arithmetic bound for cvc5 to struggle with beyond
/// whatever the function's own declared domain already required it to
/// handle.
fn try_promote_to_int64<'a>(
    def: &'a SemFunctionDef,
    fn_env: &FunctionEnv<'a>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Option<SemFunctionDef> {
    if def.sigs.len() != 1 {
        return None;
    }
    if def.return_kind != Kind::Int || def.param_kinds.iter().any(|k| *k != Kind::Int) {
        return None;
    }
    let sig = &def.sigs[0];
    // MVP scope: a fallible function's `return_kind` names only its success
    // Kind (`Fail`-ness lives in the `Fail`-wire `{i1, i64}` struct, built
    // separately at the codegen boundary) — promoting one is a fast-follow,
    // not this first cut, since the success payload's raw-vs-tagged
    // representation inside that wire isn't threaded through yet.
    if crate::semantics::tree::range_contains_fail(&sig.range) {
        return None;
    }
    let parts = sem_param_set_exprs(sig.domain.as_ref(), def.params.len()).ok()?;
    if parts
        .iter()
        .any(|part| !domain_within_int64(part, name_defs, timeout_ms))
    {
        return None;
    }

    let n = def.params.len();

    // The trial candidate: same body and *declared domain* (already proved
    // `⊆ Int64` above, so it doesn't need narrowing the way `try_split`'s
    // does — unlike `synth_def`, which always narrows both), but `range`
    // narrowed to `Int64` — this is the actual claim being tested. Distinct
    // from the permanent result below: narrowing this trial's range doesn't
    // weaken the function's real, permanent contract.
    let trial = SemFunctionDef {
        name: def.name.clone(),
        sigs: vec![SemFunctionSig {
            domain: sig.domain.clone(),
            range: var_expr("Int64", Kind::Int64, def.span),
            param_kinds: vec![Kind::Int64; n],
            return_kind: Kind::Int64,
            span: sig.span,
        }],
        params: def.params.clone(),
        body: def.body.clone(),
        param_kinds: vec![Kind::Int64; n],
        return_kind: Kind::Int64,
        span: def.span,
        compiler_generated_split: false,
    };

    let mut trial_env = fn_env.clone();
    trial_env.insert(trial.name.clone(), vec![&trial]);
    let proved = trial_fully_proves_int64(&trial, &trial_env, name_defs, timeout_ms);
    drop(trial_env);
    if !proved {
        return None;
    }

    // The real, permanent result: original domain *and* range untouched
    // (weakening a bounded function's declared range to the broader
    // `Int64` would regress provability for its own callers) — only the
    // Kind labels change, to the raw representation.
    Some(SemFunctionDef {
        name: def.name.clone(),
        sigs: vec![SemFunctionSig {
            domain: sig.domain.clone(),
            range: sig.range.clone(),
            param_kinds: vec![Kind::Int64; n],
            return_kind: Kind::Int64,
            span: sig.span,
        }],
        params: def.params.clone(),
        body: def.body.clone(),
        param_kinds: vec![Kind::Int64; n],
        return_kind: Kind::Int64,
        span: def.span,
        compiler_generated_split: false,
    })
}

/// `true` when `expr` is a bare reference to the named builtin set (`Var`
/// with no further structure) — the MVP's domain/range eligibility shape.
fn is_bare_named_set(expr: &SemExpr, name: &str) -> bool {
    matches!(&expr.kind, SemExprKind::Var(sym) if sym.0 == name)
}

fn var_expr(name: &str, kind_of: Kind, span: Span) -> SemExpr {
    SemExpr {
        kind: SemExprKind::Var(Symbol::new(name)),
        kind_of,
        span,
    }
}

/// Build a compiler-generated single-signature overload sharing `def`'s
/// params/body, with `domain`/`range` as declared and `param_kind`/
/// `return_kind` as the sole param Kind and the return Kind.
///
/// Domain and range are *independent* here on purpose: the `BigInt`
/// overload restricts its domain to `Int - Int64` (so phase 2's
/// disjointness check against the `Int64` overload holds) but must keep
/// the *original*, unbounded `Int` range — the original function's real
/// contract promises a correct result for every input, and narrowing the
/// range to `Int - Int64` too would be a false claim in general (e.g.
/// halving a huge value can land back inside `Int64`).
fn synth_def(
    def: &SemFunctionDef,
    domain: SemExpr,
    range: SemExpr,
    param_kind: Kind,
    return_kind: Kind,
) -> SemFunctionDef {
    let sig = SemFunctionSig {
        domain: Some(domain),
        range,
        param_kinds: vec![param_kind.clone()],
        return_kind: return_kind.clone(),
        span: def.span,
    };
    SemFunctionDef {
        name: def.name.clone(),
        sigs: vec![sig],
        params: def.params.clone(),
        body: def.body.clone(),
        param_kinds: vec![param_kind],
        return_kind,
        span: def.span,
        compiler_generated_split: true,
    }
}

/// Attempt the split for one function. Returns `None` when `def` isn't in
/// the MVP eligibility shape, or when the synthesized `Int64 -> Int64`
/// claim doesn't check as `Proved` — in either case `def` is left as an
/// ordinary, unsplit function.
fn try_split<'a>(
    def: &'a SemFunctionDef,
    fn_env: &FunctionEnv<'a>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Option<(SemFunctionDef, SemFunctionDef)> {
    if def.params.len() != 1 || def.sigs.len() != 1 {
        return None;
    }
    let sig = &def.sigs[0];
    let domain = sig.domain.as_ref()?;
    if !is_bare_named_set(domain, "Int") || !is_bare_named_set(&sig.range, "Int") {
        return None;
    }
    if body_contains_mul(&def.body) {
        return None;
    }

    let int64_def = synth_def(
        def,
        var_expr("Int64", Kind::Int64, def.span),
        var_expr("Int64", Kind::Int64, def.span),
        Kind::Int64,
        Kind::Int64,
    );

    // Override just this name's entry so a recursive self-call is checked
    // against the *narrower* Int64 contract as its own induction
    // hypothesis (this can prove strictly more than reusing the original
    // wide contract would); calls to any other function keep resolving
    // against their real, unmodified contracts from `fn_env`.
    let mut trial_env = fn_env.clone();
    trial_env.insert(int64_def.name.clone(), vec![&int64_def]);

    if !trial_fully_proves_int64(&int64_def, &trial_env, name_defs, timeout_ms) {
        return None;
    }

    let bigint_domain = SemExpr {
        kind: SemExprKind::SetDifference(
            Box::new(var_expr("Int", Kind::Int, def.span)),
            Box::new(var_expr("Int64", Kind::Int64, def.span)),
        ),
        kind_of: Kind::Int,
        span: def.span,
    };
    // The original range, unchanged — see `synth_def`'s doc comment for why
    // this must not also be narrowed to `Int - Int64`.
    let bigint_def = synth_def(def, bigint_domain, sig.range.clone(), Kind::Int, Kind::Int);

    Some((int64_def, bigint_def))
}

/// `true` if `body` contains a value-position `Mul` (`*`) anywhere — see
/// this module's doc comment for why that disqualifies a candidate from
/// the trial check entirely. Recurses exhaustively (no wildcard arm) so a
/// future `SemExprKind`/`SemStmt` variant forces an explicit decision here
/// rather than silently being treated as safe.
fn body_contains_mul(body: &SemFunctionBody) -> bool {
    match body {
        SemFunctionBody::Expr(e) => expr_contains_mul(e),
        SemFunctionBody::Block(stmts) => stmts.iter().any(stmt_contains_mul),
    }
}

fn stmt_contains_mul(stmt: &SemStmt) -> bool {
    match stmt {
        SemStmt::Let {
            constraint, value, ..
        }
        | SemStmt::MutLet {
            constraint, value, ..
        } => expr_contains_mul(constraint) || expr_contains_mul(value),
        SemStmt::Assign { value, .. } | SemStmt::DestructAssign { value, .. } => {
            expr_contains_mul(value)
        }
        SemStmt::DestructLet {
            tuple_constraint,
            value,
            ..
        }
        | SemStmt::DestructMutLet {
            tuple_constraint,
            value,
            ..
        } => tuple_constraint.as_ref().is_some_and(expr_contains_mul) || expr_contains_mul(value),
        SemStmt::Require { predicate, .. } | SemStmt::Assume { predicate, .. } => {
            expr_contains_mul(predicate)
        }
        SemStmt::Assert {
            predicate,
            else_clause,
            ..
        } => {
            expr_contains_mul(predicate)
                || match else_clause {
                    None => false,
                    Some(SemAssertElse::FailWith(e)) | Some(SemAssertElse::Return(e)) => {
                        expr_contains_mul(e)
                    }
                }
        }
        SemStmt::Expr(e) => expr_contains_mul(e),
        SemStmt::Block(stmts) => stmts.iter().any(stmt_contains_mul),
        SemStmt::While { cond, body, .. } => {
            expr_contains_mul(cond) || body.iter().any(stmt_contains_mul)
        }
        SemStmt::ForIn { set, body, .. } => {
            expr_contains_mul(set) || body.iter().any(stmt_contains_mul)
        }
        SemStmt::Return { value, .. } => expr_contains_mul(value),
    }
}

fn expr_contains_mul(expr: &SemExpr) -> bool {
    match &expr.kind {
        SemExprKind::Mul(_, _) => true,
        SemExprKind::IntLit(_)
        | SemExprKind::BoolLit(_)
        | SemExprKind::CharLit(_)
        | SemExprKind::Var(_)
        | SemExprKind::FailLit => false,
        SemExprKind::Add(l, r)
        | SemExprKind::DisjointUnion(l, r)
        | SemExprKind::Sub(l, r)
        | SemExprKind::SetDifference(l, r)
        | SemExprKind::CartesianProduct(l, r)
        | SemExprKind::Div(l, r) => expr_contains_mul(l) || expr_contains_mul(r),
        // The RHS is a canonicalizer function name, not an expression to recurse into.
        SemExprKind::SetQuotient(l, _canon) => expr_contains_mul(l),
        SemExprKind::BinOp { lhs, rhs, .. } => expr_contains_mul(lhs) || expr_contains_mul(rhs),
        SemExprKind::UnOp { expr, .. } => expr_contains_mul(expr),
        SemExprKind::Call { args, .. } => args.iter().any(expr_contains_mul),
        SemExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_contains_mul(cond) || expr_contains_mul(then_expr) || expr_contains_mul(else_expr)
        }
        SemExprKind::SetLit(exprs) | SemExprKind::Tuple(exprs) => {
            exprs.iter().any(expr_contains_mul)
        }
        SemExprKind::Try(e) | SemExprKind::FailWith(e) | SemExprKind::KleeneStar(e) => {
            expr_contains_mul(e)
        }
        SemExprKind::Comprehension {
            output,
            source,
            filter,
            ..
        } => {
            expr_contains_mul(output)
                || expr_contains_mul(source)
                || filter.as_deref().is_some_and(expr_contains_mul)
        }
        SemExprKind::Proj { base, .. } => expr_contains_mul(base),
        SemExprKind::Index { base, index } => expr_contains_mul(base) || expr_contains_mul(index),
    }
}
