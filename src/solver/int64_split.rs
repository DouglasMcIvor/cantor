//! int-soundness-plan phase 3, step 4a: the compiler-generated `Int64`/
//! `BigInt` overload split.
//!
//! **Solver-gated, not unconditional** (corrected 2026-07-04 — see
//! docs/int-soundness-plan.md's "The overload split" section for the
//! counterexample that ruled out the original unconditional design): a
//! function is only split when the solver *additionally* proves the
//! narrower whole-body claim `args ∈ Int64 → result ∈ Int64`, by re-running
//! the ordinary existing signature checker (`check_function`) against a
//! synthesized `Int64 -> Int64` narrowing of the same body — no new proof
//! machinery. When it proves, the `Int64` overload is sound end-to-end with
//! zero tagging anywhere inside it (every node was just proved bounded).
//! When it doesn't, no split is generated at all; the function stays a
//! single ordinary `Kind::Int` body relying on the separate per-node
//! promotion mechanism (steps 4b–4d) for correctness.
//!
//! **MVP eligibility (deliberately narrow — see int-soundness-plan.md):**
//! exactly one parameter, exactly one signature, declared domain *and*
//! range both the bare unbounded `Int` builtin, and a body containing no
//! `*` (value-position `Mul`) anywhere. Multi-parameter Cartesian domains
//! and signatures mixing `Int` with other Kinds are a fast-follow, not this
//! first cut.
//!
//! **The `Mul` restriction is a safety measure, not a design choice** — see
//! int-soundness-plan.md's "Phase 3" section for the full story: bounding a
//! nonlinear (`*`) term to the *finite but huge* `Int64` range
//! (`∃x ∈ [i64::MIN, i64::MAX]. x*x ∉ [i64::MIN, i64::MAX]`) was found to
//! make cvc5 run past its configured `tlimit` for a very long time (90+s
//! observed with `tlimit` set as low as 2000ms) — the *same* overflow
//! question over an *unconstrained* `x`/`y` (phase 1's existing per-node
//! check) returns fast, so the huge-but-finite bound specifically seems to
//! push cvc5 into a much harder code path. A background-thread watchdog
//! isn't a safe mitigation here: cvc5 isn't thread-safe even with
//! per-thread `TermManager`/`Solver` instances (see `CVC5_CALL_LOCK`'s doc
//! comment) — racing a second concurrent cvc5 call while abandoning a
//! hung one is a real segfault risk, not just slow. So for now, a body
//! containing multiplication is never attempted, regardless of whether it
//! would actually be Int64-preserving (e.g. `f(x) = x * 0` is skipped too,
//! even though it trivially would prove).

use std::collections::HashMap;

use crate::kind::Kind;
use crate::semantics::tree::{
    SemAssertElse, SemExpr, SemExprKind, SemFunctionBody, SemFunctionDef, SemFunctionSig, SemItem,
    SemStmt,
};
use crate::span::{Span, Symbol};

use super::{CheckResult, FunctionEnv, NameDefs, check_function};

/// Runs the split pass over every function in the file. Items that aren't
/// `FunctionDef`s, or don't qualify, or don't prove, pass through unchanged.
pub(super) fn generate_int64_bigint_splits(
    sem_items: Vec<SemItem>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Vec<SemItem> {
    // The real, file-wide contracts — used so a candidate body's calls to
    // any *other* function resolve against their genuine signatures during
    // the trial check below. Only the candidate's own entry is overridden,
    // per candidate, inside `try_split`.
    let mut fn_env: FunctionEnv<'_> = FunctionEnv::new();
    for item in &sem_items {
        if let SemItem::FunctionDef(def) = item {
            fn_env.entry(def.name.clone()).or_default().push(def);
        }
    }

    let mut out = Vec::with_capacity(sem_items.len());
    for item in &sem_items {
        match item {
            // MVP scope: only split a name that has *no* other FunctionDef
            // in the file already — i.e. leave any pre-existing user
            // overload set (phase 2) entirely alone. This isn't a
            // fundamental limit (the split's two synthesized domains are
            // still checked for disjointness against any sibling overload,
            // same as any other phase 2 group), it just keeps step 4a from
            // also having to reason about interactions with user-declared
            // overloading in this first cut.
            SemItem::FunctionDef(def) if fn_env.get(&def.name).is_some_and(|v| v.len() == 1) => {
                match try_split(def, &fn_env, name_defs, timeout_ms) {
                    Some((int64_def, bigint_def)) => {
                        out.push(SemItem::FunctionDef(int64_def));
                        out.push(SemItem::FunctionDef(bigint_def));
                    }
                    None => out.push(item.clone()),
                }
            }
            SemItem::FunctionDef(_) | SemItem::NameDef(_) => out.push(item.clone()),
        }
    }
    out
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

    // Throwaway side-channels: this is a probe, not the real check. Its
    // per-span verdicts must never reach the file's real `overflow_checks`/
    // `overload_resolutions` maps — if the split is generated below, the
    // normal `check_file` main loop checks `int64_def` again as an ordinary
    // item and populates those maps correctly then; if it isn't, `def`
    // alone continues through the normal loop untouched.
    let mut scratch_overflow = HashMap::new();
    let mut scratch_resolutions = HashMap::new();

    // Override just this name's entry so a recursive self-call is checked
    // against the *narrower* Int64 contract as its own induction
    // hypothesis (this can prove strictly more than reusing the original
    // wide contract would); calls to any other function keep resolving
    // against their real, unmodified contracts from `fn_env`.
    let mut trial_env = fn_env.clone();
    trial_env.insert(int64_def.name.clone(), vec![&int64_def]);

    let results = check_function(
        &int64_def,
        &trial_env,
        name_defs,
        timeout_ms,
        &mut scratch_overflow,
        &mut scratch_resolutions,
    )
    .ok()?;
    let proved = results.iter().all(|(_, r)| *r == CheckResult::Proved);
    if !proved {
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
        } => {
            tuple_constraint.as_ref().is_some_and(expr_contains_mul) || expr_contains_mul(value)
        }
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
        | SemExprKind::Var(_)
        | SemExprKind::FailLit => false,
        SemExprKind::Add(l, r)
        | SemExprKind::DisjointUnion(l, r)
        | SemExprKind::Sub(l, r)
        | SemExprKind::SetDifference(l, r)
        | SemExprKind::CartesianProduct(l, r)
        | SemExprKind::Div(l, r)
        | SemExprKind::SetQuotient(l, r) => expr_contains_mul(l) || expr_contains_mul(r),
        SemExprKind::BinOp { lhs, rhs, .. } => expr_contains_mul(lhs) || expr_contains_mul(rhs),
        SemExprKind::UnOp { expr, .. } => expr_contains_mul(expr),
        SemExprKind::Call { args, .. } => args.iter().any(expr_contains_mul),
        SemExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            expr_contains_mul(cond)
                || expr_contains_mul(then_expr)
                || expr_contains_mul(else_expr)
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
        SemExprKind::Index { base, index } => {
            expr_contains_mul(base) || expr_contains_mul(index)
        }
    }
}
