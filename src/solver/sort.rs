//! CVC5 sort computation and cross-kind union datatype helpers.
//!
//! This module answers the question "what CVC5 sort does this Cantor set
//! expression have?" and provides the tools to build cross-kind union
//! algebraic datatypes, flatten union/product AST nodes, and coerce
//! expression-level CVC5 terms into a target union DT sort.
//!
//! Nothing here touches `Solver`, `Env`, or `BuiltinObligation` — those
//! are expression-encoding concerns that live in `encode.rs`.

use cvc5::{DatatypeConstructorDecl, Kind, Sort, Term, TermManager};

use crate::{
    ast::{BinOp, Expr, ExprKind},
    kind::{Kind as ValKind, set_kind as val_set_kind},
};

use super::membership::DistinctPreds;

// ── AST flattening ────────────────────────────────────────────────────────────

/// Flatten a left-associative `A * B * C` product into `[A, B, C]`.
pub(crate) fn flatten_product(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs } => {
            let mut parts = flatten_product(lhs);
            parts.push(rhs);
            parts
        }
        _ => vec![expr],
    }
}

/// Flatten a left-associative `A | B | C` or `A + B + C` into `[A, B, C]`.
///
/// Used when building a CVC5 algebraic datatype for a cross-kind union so that
/// `(A | B) | C` gives `[A, B, C]` rather than `[[A, B], C]`.
pub(crate) fn flatten_any_union(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let mut arms = flatten_any_union(lhs);
            arms.push(rhs);
            arms
        }
        _ => vec![expr],
    }
}

// ── Cross-kind union datatype naming ─────────────────────────────────────────

/// Canonical CVC5 constructor name for a cross-kind union arm, derived from
/// its `ValKind`.
///
/// Used both when creating the datatype sort in `set_sort` and when looking up
/// the right constructor in `membership_constraint`, so the names must match
/// exactly.
pub(crate) fn arm_ctor_name(k: &ValKind) -> String {
    match k {
        ValKind::Int           => "ck_Int".to_string(),
        ValKind::Bool          => "ck_Bool".to_string(),
        ValKind::Fail          => "ck_Fail".to_string(),
        ValKind::Set(_)        => "ck_Set".to_string(),
        ValKind::Union(_)      => "ck_Union".to_string(),
        ValKind::Tuple(inner)  => {
            let s = inner.iter().map(arm_ctor_name).collect::<Vec<_>>().join("_");
            format!("ck_T_{s}")
        }
        ValKind::TaggedUnion(arms) => {
            let s = arms.iter().map(arm_ctor_name).collect::<Vec<_>>().join("_");
            format!("ck_TU_{s}")
        }
        ValKind::Vector(elem) => format!("ck_V_{}", arm_ctor_name(elem)),
    }
}

/// Constructor name for a union arm, with distinct-set awareness.
///
/// Distinct-set arms get `"ck_D_{Name}"` so they never collide with `"ck_Int"`
/// from scalar arms — even though both would produce `ValKind::Int` via
/// `val_set_kind`.  All other arms delegate to `arm_ctor_name`.
///
/// This must be used wherever `arm_ctor_name` was previously used for
/// individual arms in the union-datatype pipeline (creation in
/// `build_union_datatype_sort` and lookup in `membership_constraint_for_dt`)
/// so the names always match.
pub(crate) fn arm_ctor_name_for_arm<'tm>(
    arm_expr: &Expr,
    distinct_preds: &DistinctPreds<'tm>,
) -> String {
    if let ExprKind::Var(sym) = &arm_expr.kind {
        if distinct_preds.contains_key(sym) {
            return format!("ck_D_{}", sym.0);
        }
    }
    arm_ctor_name(&val_set_kind(arm_expr))
}

// ── Cross-kind union datatype construction ───────────────────────────────────
//
// To add a new CVC5 sort (e.g. Float32, Float64) as a union arm in the future:
//   1. kind.rs::set_kind      — add the new ExprKind → Kind::Float variant
//   2. set_sort (below)       — add the new ExprKind → tm.mk_float_sort() arm
//   3. arm_ctor_name (below)  — add ValKind::Float → "ck_F32"/"ck_F64" name
//   4. membership_constraint  — add a Var("Float32")/… arm in membership.rs
//   5. mod.rs cex extraction  — add ValKind::Float placeholder (0 for now)
// No changes needed in build_union_datatype_sort, coerce_to_union_dt, or
// maybe_coerce — they are now sort-agnostic.

/// Build a CVC5 algebraic datatype sort for a cross-kind union.
///
/// Each arm gets **one** constructor with **one** selector whose sort is the
/// arm's natural CVC5 sort (from `set_sort`).  This is sort-agnostic: it works
/// for integer, boolean, tuple, sequence, distinct-sort, or any future sort
/// without modification.
///
/// - Distinct-set arms: selector sort is the set's uninterpreted sort.
/// - All other arms: selector sort is `set_sort(arm_expr)`.
///
/// Arms are listed in the order determined by `flatten_any_union`.
fn build_union_datatype_sort<'tm>(
    tm: &'tm TermManager,
    arms: &[&Expr],
    distinct_preds: &DistinctPreds<'tm>,
) -> Sort<'tm> {
    let arm_infos: Vec<(String, Sort<'_>)> = arms.iter().map(|arm_expr| {
        if let ExprKind::Var(sym) = &arm_expr.kind {
            if let Some(info) = distinct_preds.get(sym) {
                return (format!("ck_D_{}", sym.0), info.sort.clone());
            }
        }
        let ctor_name = arm_ctor_name(&val_set_kind(arm_expr));
        let sort = set_sort(tm, arm_expr, distinct_preds)
            .expect("build_union_datatype_sort: arm has no representable CVC5 sort");
        (ctor_name, sort)
    }).collect();

    let dt_name = format!(
        "CKU_{}",
        arm_infos.iter().map(|(name, _)| name.as_str()).collect::<Vec<_>>().join("_")
    );
    let mut dt_decl = tm.mk_dt_decl(&dt_name, false);
    for (ctor_name, sel_sort) in &arm_infos {
        let mut ctor: DatatypeConstructorDecl<'_> = tm.mk_dt_cons_decl(ctor_name);
        ctor.add_selector("f0", sel_sort.clone());
        dt_decl.add_constructor(&ctor);
    }
    tm.mk_dt_sort(&dt_decl)
}

// ── Sort coercion helpers ─────────────────────────────────────────────────────

/// Wrap `val` into the matching constructor of `dt_sort` (a cross-kind union
/// algebraic datatype built by `build_union_datatype_sort`).
///
/// Finds the constructor whose single selector has a codomain sort equal to
/// `val.sort()`, then wraps `val` directly: `ApplyConstructor(ctor, [val])`.
/// This is sort-agnostic — no flattening or sort-to-kind mapping needed.
///
/// Returns `Err` if no constructor's selector sort matches `val.sort()`.
fn coerce_to_union_dt<'tm>(
    tm: &'tm TermManager,
    val: Term<'tm>,
    dt_sort: &Sort<'tm>,
) -> Result<Term<'tm>, String> {
    let val_sort = val.sort();
    let dt = dt_sort.datatype();
    let ctor = (0..dt.num_constructors())
        .map(|i| dt.constructor(i))
        .find(|c| c.num_selectors() == 1 && c.selector(0).codomain_sort() == val_sort)
        .ok_or_else(|| format!(
            "coerce_to_union_dt: no constructor with selector sort matching {:?} \
             in target datatype — the value's sort is not an arm of the declared union",
            val_sort
        ))?;
    Ok(tm.mk_term(Kind::ApplyConstructor, &[ctor.term(), val]))
}

/// Coerce `term` to `coerce_to` sort if the target is a cross-kind union DT.
///
/// Tries to match `term.sort()` against a constructor selector sort in the
/// target DT.  Passes through unchanged if:
/// - no `coerce_to` target,
/// - already the right sort,
/// - target is not a cross-kind DT (non-DT or plain tuple).
///
/// Used at the end of `encode_expr` (general case) and at early-return sites
/// inside `encode_call` (constructor calls that bypass the end-of-function
/// coerce block).
pub(crate) fn maybe_coerce<'tm>(
    tm: &'tm TermManager,
    term: Term<'tm>,
    coerce_to: &Option<Sort<'tm>>,
) -> Result<Term<'tm>, String> {
    let Some(dt_sort) = coerce_to.as_ref() else { return Ok(term); };
    if term.sort() == *dt_sort || !dt_sort.is_dt() || dt_sort.is_tuple() {
        return Ok(term);
    }
    // Attempt to wrap the term in the constructor of the cross-kind union DT
    // whose selector sort matches term.sort().  Returns the term unchanged on
    // failure (sort mismatch — caller is responsible for detecting incompatibility).
    Ok(coerce_to_union_dt(tm, term.clone(), dt_sort).unwrap_or(term))
}

// ── Set-expression → CVC5 sort ────────────────────────────────────────────────

/// SMT sort for a set expression.
///
/// Cross-kind unions (one arm is a tuple, another is a scalar) are encoded as
/// a CVC5 algebraic datatype with one constructor per arm; `membership_constraint`
/// in `membership.rs` uses `ApplyTester` / `ApplySelector` to check membership.
///
/// For example, `(Nat * Nat) | Nat` becomes a CVC5 datatype:
/// ```text
/// CKU_ck_T_ck_Int_ck_Int_ck_Int {
///   ck_T_ck_Int_ck_Int(f0: Int, f1: Int),
///   ck_Int(f0: Int),
/// }
/// ```
/// with `t ∈ (Nat * Nat) | Nat ↔ (is_ck_T(t) ∧ f0(t) ≥ 0 ∧ f1(t) ≥ 0) ∨ (is_ck_Int(t) ∧ f0(t) ≥ 0)`.
///
/// Every `ExprKind` variant that can appear in set-expression position is listed
/// explicitly.  Adding a new `ExprKind` to the AST will cause a compile error
/// here, forcing a conscious decision about its CVC5 sort rather than silently
/// falling through to integer sort.
pub(crate) fn set_sort<'tm>(
    tm: &'tm TermManager,
    set_expr: &Expr,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<Sort<'tm>> {
    Some(match &set_expr.kind {
        // Bool has its own CVC5 boolean sort.
        ExprKind::Var(sym) if sym.0 == "Bool" => tm.boolean_sort(),
        // Distinct sets each have their own CVC5 uninterpreted sort.
        ExprKind::Var(sym) => {
            if let Some(info) = distinct_preds.get(sym) {
                info.sort.clone()
            } else {
                // All other named sets (Nat, NatPos, Int, Int8…Int64, …) → integer.
                tm.integer_sort()
            }
        }
        // Set literals {0}, {1, 2, 3} — elements are integers.
        ExprKind::SetLit(_) => tm.integer_sort(),
        // Comprehensions {x for x in S} — elements are integers.
        ExprKind::Comprehension { .. } => tm.integer_sort(),
        // Built-in set constructors Set(Int), Set(Bool) — variable holds an i64 pointer.
        ExprKind::Call { .. } => tm.integer_sort(),
        // `A * B * C` — Cartesian product → CVC5 tuple sort.
        ExprKind::BinOp { op: BinOp::Mul, .. } => {
            let parts = flatten_product(set_expr);
            let sorts: Vec<Sort<'_>> = parts.iter()
                .map(|p| set_sort(tm, p, distinct_preds))
                .collect::<Option<Vec<_>>>()?;
            tm.mk_tuple_sort(&sorts)
        }
        // Set diff (`-`), symmetric diff (`^`), intersection (`&`): elements live in
        // the same space as the LHS (e.g. `Nat* - {}` is still a set of sequences).
        // Propagate the LHS sort; fall through to integer sort if the LHS has no
        // representable CVC5 sort.
        ExprKind::BinOp { op: BinOp::Sub | BinOp::SymDiff | BinOp::Intersect, lhs, .. } => {
            return set_sort(tm, lhs, distinct_preds);
        }
        // Union (`|`) and disjoint union (`+`).
        // Cross-kind (tuple arm ∪ scalar, sequence arm ∪ non-same-sequence, or
        // distinct-sort ∪ anything different) → CVC5 algebraic datatype.
        // Same-kind scalar unions (Bool | Nat, Int | NatPos, Nat* | Int*) → no DT.
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let ls = set_sort(tm, lhs, distinct_preds)?;
            let rs = set_sort(tm, rhs, distinct_preds)?;
            let is_distinct_sort = |s: &Sort<'_>| distinct_preds.values().any(|i| &i.sort == s);
            // Sequence arms with the same sort are "same-kind" (e.g. Nat* | Int* both
            // give Seq<Int>); sequences with different element sorts, or one sequence and
            // one non-sequence, are cross-kind and need a DT.
            let seq_is_cross_kind = (ls.is_sequence() || rs.is_sequence()) && ls != rs;
            if ls.is_tuple() || rs.is_tuple() || ls.is_dt() || rs.is_dt()
                || is_distinct_sort(&ls) || is_distinct_sort(&rs)
                || seq_is_cross_kind
            {
                // Cross-kind: build a CVC5 algebraic datatype with one constructor per arm.
                let arms = flatten_any_union(set_expr);
                return Some(build_union_datatype_sort(tm, &arms, distinct_preds));
            }
            // Both arms are plain scalar (Int-family) or same-sort sequences;
            // integer sort covers the scalar case, and the sequence case uses OR of constraints.
            if ls.is_sequence() { ls } else { tm.integer_sort() }
        }
        // Value-position BinOp operators must not appear in set-expression context.
        ExprKind::BinOp {
            op: BinOp::Div | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le
                | BinOp::Gt | BinOp::Ge | BinOp::And | BinOp::Or
                | BinOp::In | BinOp::NotIn | BinOp::Concat,
            ..
        } => unreachable!(
            "set_sort: value-position BinOp in set-expression context: {:?}",
            set_expr.kind
        ),
        // `X*` — Kleene star: variable-length sequence of X.
        // Encoded as the CVC5 sequence sort `(Seq elem)` via the theory of sequences.
        // The element sort is derived recursively; if the element set has no
        // representable CVC5 sort we propagate None so callers surface Unknown.
        ExprKind::KleeneStar(inner) => {
            let elem = set_sort(tm, inner, distinct_preds)?;
            tm.mk_sequence_sort(elem)
        }
        // Value-position ExprKind variants must never appear as set expressions.
        // Listed explicitly so adding a new ExprKind causes a compile error here.
        ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::UnOp { .. }
        | ExprKind::If { .. } | ExprKind::Tuple(_) | ExprKind::Proj { .. }
        | ExprKind::Index { .. }
        | ExprKind::Try(_) | ExprKind::FailLit | ExprKind::FailWith(_) => unreachable!(
            "set_sort: value-position expression in set-expression context: {:?}",
            set_expr.kind
        ),
    })
}

// ── Range-specific sort helpers ───────────────────────────────────────────────

/// Return the success-only arm of a fallible range.
///
/// Strips `Fail` and `Fail * Y` arms from a union, returning the sub-expression
/// that represents the success set.  Used by the `Try` encoding to assert that,
/// after `?` propagation, the result lies in the success set.
///
/// Examples:
///   `Nat | Fail`              → `Some(Nat)`
///   `Nat | (Fail * Y)`        → `Some(Nat)`
///   `Nat | Fail | (Fail * Y)` → `Some(Nat)`
///   `Fail`                    → `None`
pub(crate) fn success_arm_of_range(range: &Expr) -> Option<&Expr> {
    fn is_fail_arm(e: &Expr) -> bool {
        matches!(&e.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            || matches!(
                &e.kind,
                ExprKind::BinOp { op: BinOp::Mul, lhs, .. }
                    if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            )
    }
    if is_fail_arm(range) { return None; }
    if let ExprKind::BinOp { op: BinOp::Union, lhs, rhs } = &range.kind {
        if is_fail_arm(rhs) { return success_arm_of_range(lhs); }
        if is_fail_arm(lhs) { return success_arm_of_range(rhs); }
    }
    Some(range)
}

/// SMT sort for a range expression.
///
/// Strips `Fail * Y` union wrappers to find the success sort, then delegates
/// to `set_sort` (which handles cross-kind unions via datatypes).
pub(crate) fn set_sort_for_range<'tm>(
    tm: &'tm TermManager,
    range: &Expr,
    distinct_preds: &DistinctPreds<'tm>,
) -> Option<Sort<'tm>> {
    match &range.kind {
        ExprKind::Var(sym) if sym.0 == "Fail" => Some(tm.integer_sort()),
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let is_fail_product = |e: &Expr| matches!(
                &e.kind,
                ExprKind::BinOp { op: BinOp::Mul, lhs, .. }
                    if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            );
            if is_fail_product(rhs) { return set_sort_for_range(tm, lhs, distinct_preds); }
            if is_fail_product(lhs) { return set_sort_for_range(tm, rhs, distinct_preds); }
            set_sort(tm, range, distinct_preds)
        }
        _ => set_sort(tm, range, distinct_preds),
    }
}

/// True if the range (after stripping Fail/Union wrappers) is a product set.
pub(crate) fn is_product_range(range: &Expr) -> bool {
    match &range.kind {
        ExprKind::BinOp { op: BinOp::Mul, .. } => true,
        ExprKind::BinOp { op: BinOp::Union | BinOp::Add, lhs, rhs } => {
            let is_fail_product = |e: &Expr| matches!(
                &e.kind,
                ExprKind::BinOp { op: BinOp::Mul, lhs, .. }
                    if matches!(&lhs.kind, ExprKind::Var(sym) if sym.0 == "Fail")
            );
            if is_fail_product(rhs) { return is_product_range(lhs); }
            if is_fail_product(lhs) { return is_product_range(rhs); }
            // Non-fail union: no single arm defines the product structure.
            // Previously this silently returned is_product_range(lhs), which caused
            // (Nat * Nat) | Nat to be treated as a product range even though it isn't.
            false
        }
        ExprKind::Var(sym) if sym.0 == "Fail" => false,
        _ => false,
    }
}

