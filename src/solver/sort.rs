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
    ast::BinOp,
    kind::Kind as ValKind,
    semantics::tree::{SemExpr, SemExprKind, flatten_any_union, flatten_cartesian_product},
    span::Symbol,
};

use super::NameDefs;
use super::membership::{DistinctPreds, SolverPreds};

/// Map a scalar element `ValKind` to its CVC5 sort — used by `set_sort`'s
/// `SetLit` arm so a domain literal's sort follows its elaborated element
/// Kind (`kind::set_kind`'s `SetLit` arm) instead of assuming integer.
///
/// Returns `None` for structural/heterogeneous kinds (`Tuple`, `TaggedUnion`,
/// `Vector`, `Set`) — a mixed-kind or structural set literal has no single
/// natural sort here; callers propagate `None` to `Unknown` rather than
/// guessing, same as any other not-yet-representable sort in this module.
fn scalar_kind_sort<'tm>(
    tm: &'tm TermManager,
    kind: &ValKind,
    distinct_preds: &SolverPreds<'tm>,
) -> Option<Sort<'tm>> {
    Some(match kind {
        ValKind::Bool => tm.boolean_sort(),
        ValKind::Int | ValKind::Int64 => tm.integer_sort(),
        ValKind::Char => distinct_preds.get(&Symbol::new("Char"))?.sort.clone(),
        ValKind::Fail => distinct_preds.get(&Symbol::new("Fail"))?.sort.clone(),
        ValKind::None => distinct_preds.get(&Symbol::new("None"))?.sort.clone(),
        ValKind::Signed32 => distinct_preds
            .wrapping
            .get(&Symbol::new("Signed32"))?
            .d_sort
            .clone(),
        ValKind::Unsigned32 => distinct_preds
            .wrapping
            .get(&Symbol::new("Unsigned32"))?
            .d_sort
            .clone(),
        ValKind::Tuple(_) | ValKind::TaggedUnion(_) | ValKind::Vector(_) | ValKind::Set(_) => {
            return None;
        }
    })
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
        // The solver reasons over unbounded ℤ regardless of raw-vs-tagged
        // codegen representation (int-soundness-plan phase 3) — Int64 is
        // just Int as far as CVC5 sorts/constructors are concerned.
        ValKind::Int | ValKind::Int64 => "ck_Int".to_string(),
        ValKind::Bool => "ck_Bool".to_string(),
        ValKind::Fail => "ck_Fail".to_string(),
        ValKind::None => "ck_None".to_string(),
        // Each already has its own unique Kind (unlike `distinct`, which
        // always reports `ValKind::Int` and needs `arm_ctor_name_for_arm`'s
        // symbol-based disambiguation instead) — no name collision risk.
        ValKind::Signed32 => "ck_Signed32".to_string(),
        ValKind::Unsigned32 => "ck_Unsigned32".to_string(),
        ValKind::Char => "ck_Char".to_string(),
        ValKind::Set(_) => "ck_Set".to_string(),
        ValKind::Tuple(inner) => {
            let s = inner
                .iter()
                .map(arm_ctor_name)
                .collect::<Vec<_>>()
                .join("_");
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
/// `Kind` alone. All other arms delegate to `arm_ctor_name` using the arm's
/// already-elaborated `kind_of`.
///
/// This must be used wherever `arm_ctor_name` was previously used for
/// individual arms in the union-datatype pipeline (creation in
/// `build_union_datatype_sort` and lookup in `membership_constraint_for_dt`)
/// so the names always match.
pub(crate) fn arm_ctor_name_for_arm<'tm>(
    arm_expr: &SemExpr,
    distinct_preds: &DistinctPreds<'tm>,
) -> String {
    if let SemExprKind::Var(sym) = &arm_expr.kind
        && distinct_preds.contains_key(sym)
    {
        return format!("ck_D_{}", sym.0);
    }
    arm_ctor_name(&arm_expr.kind_of)
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
pub(super) fn build_union_datatype_sort<'tm>(
    tm: &'tm TermManager,
    arms: &[&SemExpr],
    distinct_preds: &SolverPreds<'tm>,
    name_defs: &NameDefs,
) -> Sort<'tm> {
    let arm_infos: Vec<(String, Sort<'_>)> = arms
        .iter()
        .map(|arm_expr| {
            if let SemExprKind::Var(sym) = &arm_expr.kind
                && let Some(info) = distinct_preds.get(sym)
            {
                return (format!("ck_D_{}", sym.0), info.sort.clone());
            }
            let ctor_name = arm_ctor_name(&arm_expr.kind_of);
            let sort = set_sort(tm, arm_expr, distinct_preds, name_defs)
                .expect("build_union_datatype_sort: arm has no representable CVC5 sort");
            (ctor_name, sort)
        })
        .collect();

    let dt_name = format!(
        "CKU_{}",
        arm_infos
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>()
            .join("_")
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
        .ok_or_else(|| {
            format!(
                "coerce_to_union_dt: no constructor with selector sort matching {:?} \
             in target datatype — the value's sort is not an arm of the declared union",
                val_sort
            )
        })?;
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
    let Some(dt_sort) = coerce_to.as_ref() else {
        return Ok(term);
    };
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
/// Every `SemExprKind` variant that can appear in set-expression position is
/// listed explicitly. Adding a new variant to the AST/SemanticTree will cause
/// a compile error here, forcing a conscious decision about its CVC5 sort
/// rather than silently falling through to integer sort.
pub(crate) fn set_sort<'tm>(
    tm: &'tm TermManager,
    set_expr: &SemExpr,
    distinct_preds: &SolverPreds<'tm>,
    name_defs: &NameDefs,
) -> Option<Sort<'tm>> {
    Some(match &set_expr.kind {
        // Signed32/Unsigned32 (docs/wrapping-and-quotient-sets-plan.md) each
        // have their own CVC5 uninterpreted sort, exactly like a distinct
        // set — but registered in `wrapping`, not `distinct` (they're
        // language builtins with no `NameDef`, resolved by `kind_of` alone).
        SemExprKind::Var(sym)
            if matches!(set_expr.kind_of, ValKind::Signed32 | ValKind::Unsigned32) =>
        {
            distinct_preds
                .wrapping
                .get(sym)
                .expect("Signed32/Unsigned32 must be registered as builtin wrapping sorts")
                .d_sort
                .clone()
        }
        // Distinct sets each have their own CVC5 uninterpreted sort — checked
        // before the `Bool`/`Int` fallbacks below, and *before* looking at
        // `kind_of` at all, since a distinct set's basis Kind can now be
        // anything (`Bool` included, now that `distinct` is no longer
        // Int-only) and must never be confused with the builtin `Bool`/`Int`
        // sort itself just because it happens to share that Kind.
        SemExprKind::Var(sym) if distinct_preds.get(sym).is_some() => distinct_preds
            .get(sym)
            .expect("checked by the match guard above")
            .sort
            .clone(),
        // Bool has its own CVC5 boolean sort.
        SemExprKind::Var(_) if set_expr.kind_of == ValKind::Bool => tm.boolean_sort(),
        // All other named sets (Nat, NatPos, Int, Int8…Int64, …) → integer.
        SemExprKind::Var(_) => tm.integer_sort(),
        // Set literals {0}, {1, 2, 3}, {'a', 'b'} — the sort follows the
        // elaborated element Kind (`kind::set_kind`'s `SetLit` arm), not a
        // hardcoded integer, so e.g. a homogeneous Char literal set gets
        // Char's own uninterpreted sort. Heterogeneous/structural element
        // kinds propagate `None` (Unknown) — not yet supported here.
        SemExprKind::SetLit(_) => {
            return scalar_kind_sort(tm, &set_expr.kind_of, distinct_preds);
        }
        // Comprehensions {x for x in S if P(x)} — for the identity-output
        // shape every real comprehension in domain position uses (the only
        // shape `comprehension_membership`'s own membership check supports
        // — see membership.rs), an element's sort is exactly `S`'s own
        // element sort (previously hardcoded to `integer_sort()`, silently
        // wrong for e.g. a guard/constructor-pattern comprehension whose
        // source is a `distinct`-sorted set like `Shape`; every prior
        // Int-sourced comprehension keeps the exact same sort here, since
        // `set_sort(Nat) == integer_sort()` already).
        SemExprKind::Comprehension { source, .. } => {
            return set_sort(tm, source, distinct_preds, name_defs);
        }
        // Built-in set constructors Set(Int), Set(Bool) — variable holds an i64 pointer.
        SemExprKind::Call { .. } => tm.integer_sort(),
        // `A * B * C` — Cartesian product → CVC5 tuple sort.
        SemExprKind::CartesianProduct(..) => {
            let parts = flatten_cartesian_product(set_expr);
            let sorts: Vec<Sort<'_>> = parts
                .iter()
                .map(|p| set_sort(tm, p, distinct_preds, name_defs))
                .collect::<Option<Vec<_>>>()?;
            tm.mk_tuple_sort(&sorts)
        }
        // Set diff (`-`) and intersection (`&`): the result is a subset of A, so its
        // CVC5 sort is the LHS sort (e.g. `Nat* - {}` is still a set of sequences).
        SemExprKind::SetDifference(lhs, _) => {
            return set_sort(tm, lhs, distinct_preds, name_defs);
        }
        SemExprKind::BinOp {
            op: BinOp::Intersect,
            lhs,
            ..
        } => {
            return set_sort(tm, lhs, distinct_preds, name_defs);
        }
        // Symmetric diff (`^`): the result contains elements from EITHER side.
        // When both sides have the same CVC5 sort, that sort suffices.
        SemExprKind::BinOp {
            op: BinOp::SymDiff,
            lhs,
            rhs,
        } => {
            let lhs_sort = set_sort(tm, lhs, distinct_preds, name_defs)?;
            let rhs_sort = set_sort(tm, rhs, distinct_preds, name_defs)?;
            if lhs_sort == rhs_sort {
                return Some(lhs_sort);
            }
            // Exactly one side is a Kleene-star sequence whose *element* sort matches
            // the other side's natural sort (scalar) or all of its tuple components
            // (product) — the existing sequence-unification bridges
            // (`lift_sequence_into_atomic` / scalar-coercion in `membership_constraint`)
            // already make the other side representable as a length/element check on
            // the sequence, so the sequence sort alone suffices — no wrapper datatype.
            // e.g. `Nat* ^ Int` → `Seq Int` (Int embeds as length-1 sequences);
            // `(Nat * Nat) ^ Int` → `Seq Int` (both sides embed via their Int leaves).
            if lhs_sort.is_sequence() != rhs_sort.is_sequence() {
                let (seq_sort, other_sort) = if lhs_sort.is_sequence() {
                    (&lhs_sort, &rhs_sort)
                } else {
                    (&rhs_sort, &lhs_sort)
                };
                let elem = seq_sort.sequence_element_sort();
                let bridges = *other_sort == elem
                    || (other_sort.is_tuple()
                        && other_sort.tuple_element_sorts().iter().all(|s| *s == elem));
                if bridges {
                    return Some(seq_sort.clone());
                }
            }
            // Otherwise the two sides can never share a representable value under any
            // existing coercion (Bool vs Int-family, a distinct sort vs anything, a
            // tuple vs a scalar with no Kleene-star in sight, or two sequences with
            // different element sorts) — so they're provably disjoint and `A ^ B`
            // literally equals `A ∪ B` (XOR of disjoint sets = OR). Reuse the same
            // cross-kind tagged datatype as `|`.
            return Some(build_union_datatype_sort(
                tm,
                &[lhs.as_ref(), rhs.as_ref()],
                distinct_preds,
                name_defs,
            ));
        }
        // Union (`|`) and disjoint union (`+`).
        // Cross-kind (tuple arm ∪ scalar, sequence arm ∪ non-same-sequence,
        // distinct-sort ∪ anything different, or Bool ∪ Int-family) → CVC5
        // algebraic datatype. Same-kind unions (Int | NatPos, Nat* | Int*,
        // and — as of the `distinct`-basis generalization — two arms with
        // the *identical* tuple/DT sort, e.g. `(Nat*Nat) | (Nat*Nat)`) → no
        // DT: `kind::union_if_distinct` already dedups an identical-Kind
        // pair to a bare Kind with no tag, so `set_sort` must agree, the
        // same way it already agrees for the sequence/Bool cases just below
        // (both explicitly check `ls != rs`/arm-family mismatch rather than
        // "either side has this shape at all"). Before this was fixed, ANY
        // tuple-vs-tuple union forced a DT unconditionally, even identical
        // ones — silently wrong: a plain `(Nat*Nat)|(Nat*Nat)` projection
        // came back a fabricated counterexample, and a `distinct` set with
        // two same-shape tuple-arm labels crashed `cvc5` outright (`ApplyUf`
        // handed a bare tuple where the union DT sort was expected — a raw
        // C++-level abort, not even a catchable panic).
        SemExprKind::BinOp {
            op: BinOp::Union,
            lhs,
            rhs,
        }
        | SemExprKind::DisjointUnion(lhs, rhs) => {
            let ls = set_sort(tm, lhs, distinct_preds, name_defs)?;
            let rs = set_sort(tm, rhs, distinct_preds, name_defs)?;
            // "Opaque" = distinct-set sort or wrapping-sort (Signed32/
            // Unsigned32) — both are mutually-disjoint uninterpreted sorts
            // that always need a real tagged wrapper when unioned with
            // anything else, the same reasoning for both.
            let is_distinct_sort = |s: &Sort<'_>| {
                distinct_preds.values().any(|i| &i.sort == s)
                    || distinct_preds.wrapping.values().any(|i| &i.d_sort == s)
            };
            // Sequence arms with the same sort are "same-kind" (e.g. Nat* | Int* both
            // give Seq<Int>); sequences with different element sorts, or one sequence and
            // one non-sequence, are cross-kind and need a DT.
            let seq_is_cross_kind = (ls.is_sequence() || rs.is_sequence()) && ls != rs;
            // Bool and Int are disjoint value domains in Cantor (no implicit 0/1
            // conversion) — one boolean arm and one non-boolean arm always needs a
            // real tagged wrapper, the same as a tuple/scalar mix.
            let bool_is_cross_kind = ls.is_boolean() != rs.is_boolean();
            // Tuple/DT arms are "same-kind" only when *identical* — mirrors
            // `seq_is_cross_kind` exactly (see the doc comment above this arm).
            let tuple_is_cross_kind = (ls.is_tuple() || rs.is_tuple()) && ls != rs;
            let dt_is_cross_kind = (ls.is_dt() || rs.is_dt()) && ls != rs;
            // Deliberately *not* forcing a DT here for every `DisjointUnion`
            // regardless of `ls == rs`, even though `kind.rs`'s `BinOp::Add`
            // arm always reports `Kind::TaggedUnion` — tried that first and
            // it broke a wide swath of already-shipped, already-tested
            // same-sort `+` domain/range proofs unrelated to `distinct`
            // entirely (`{0} + NatPos -> Nat`-style signatures in
            // `tests/solver/membership.rs`/`set_ops.rs`): once a same-sort
            // `+`-value's *sort* is a DT, proving a DT-sorted parameter
            // satisfies a plain scalar return Kind (`x ∈ Nat`) hits the same
            // "narrow a cross-kind value into one arm" gap the backlog
            // already tracks as open (`from()` not narrowing into a specific
            // arm) — so this would have silently traded working code for a
            // different, bigger, deliberately-deferred gap. Labeled
            // `distinct` unions *do* need the forced tag (a label is
            // meaningless without one) — that's done narrowly at
            // `solver::preds::build_distinct_preds`'s basis-sort computation
            // instead, which only affects a `Distinct` def's own `mk_D`/
            // `from_D` sort, not this general-purpose `set_sort` used for
            // ordinary domain/range set expressions everywhere else.
            if tuple_is_cross_kind
                || dt_is_cross_kind
                || is_distinct_sort(&ls)
                || is_distinct_sort(&rs)
                || seq_is_cross_kind
                || bool_is_cross_kind
            {
                // Cross-kind: build a CVC5 algebraic datatype with one constructor per arm.
                let arms = flatten_any_union(set_expr);
                return Some(build_union_datatype_sort(
                    tm,
                    &arms,
                    distinct_preds,
                    name_defs,
                ));
            }
            // Both arms are the same underlying sort (Int-family scalars, matching
            // sequences, or both boolean) — no wrapper needed.
            ls
        }
        // `X*` — Kleene star: variable-length sequence of X.
        // Encoded as the CVC5 sequence sort `(Seq elem)` via the theory of sequences.
        // The element sort is derived recursively; if the element set has no
        // representable CVC5 sort we propagate None so callers surface Unknown.
        SemExprKind::KleeneStar(inner) => {
            let elem = set_sort(tm, inner, distinct_preds, name_defs)?;
            tm.mk_sequence_sort(elem)
        }
        // Value-position-only variants must never appear in set-expression context.
        // Listed explicitly so adding a new SemExprKind causes a compile error here.
        // `L / canon` — quotient values live in the same sort as their
        // canonical representative, i.e. `L`'s own sort (no wrapper, no new
        // sort — see docs/wrapping-and-quotient-sets-plan.md's "Runtime
        // representation" note). The canonicalizer name itself has no sort.
        SemExprKind::SetQuotient(lhs, _canon) => {
            return set_sort(tm, lhs, distinct_preds, name_defs);
        }
        SemExprKind::IntLit(_)
        | SemExprKind::BoolLit(_)
        | SemExprKind::CharLit(_)
        | SemExprKind::Add(..)
        | SemExprKind::Sub(..)
        | SemExprKind::Mul(..)
        | SemExprKind::Div(..)
        | SemExprKind::BinOp { .. }
        | SemExprKind::UnOp { .. }
        | SemExprKind::If { .. }
        | SemExprKind::Tuple(_)
        | SemExprKind::Proj { .. }
        | SemExprKind::Index { .. }
        | SemExprKind::Try(_)
        | SemExprKind::FailLit
        | SemExprKind::FailWith(_)
        | SemExprKind::NoneLit => unreachable!(
            "set_sort: value-position expression in set-expression context: {:?}",
            set_expr.kind
        ),
    })
}

// ── Range-specific sort helpers ───────────────────────────────────────────────

/// Return the success-only arm of a fallible range.
///
/// Strips `Fail`, `Fail * Y`, and bare `None` arms from a union, returning
/// the sub-expression that represents the success set. Used by the `Try`
/// encoding to assert that, after `?` propagation, the result lies in the
/// success set.
///
/// Examples:
///   `Nat | Fail`                 → `Some(Nat)`
///   `Nat | (Fail * Y)`           → `Some(Nat)`
///   `Nat | Fail | (Fail * Y)`    → `Some(Nat)`
///   `Nat | Fail | None`          → `Some(Nat)`
///   `Fail`                       → `None`
pub(crate) fn success_arm_of_range(range: &SemExpr) -> Option<&SemExpr> {
    fn is_propagation_arm(e: &SemExpr) -> bool {
        matches!(&e.kind, SemExprKind::Var(sym) if sym.0 == "Fail" || sym.0 == "None")
            || matches!(
                &e.kind,
                SemExprKind::CartesianProduct(lhs, _)
                    if matches!(&lhs.kind, SemExprKind::Var(sym) if sym.0 == "Fail")
            )
    }
    if is_propagation_arm(range) {
        return None;
    }
    if let SemExprKind::BinOp {
        op: BinOp::Union,
        lhs,
        rhs,
    } = &range.kind
    {
        if is_propagation_arm(rhs) {
            return success_arm_of_range(lhs);
        }
        if is_propagation_arm(lhs) {
            return success_arm_of_range(rhs);
        }
    }
    Some(range)
}

/// Narrow a `?`-ed call result down to just its success value.
///
/// `result_var` (from `encode_call`) is sorted as the *whole* callee range —
/// a cross-kind datatype whenever the range has a `Fail`-shaped arm, which is
/// always, now that `Fail` is a distinct sort like any other (see
/// `build_distinct_preds`). The caller has already asserted, as a solver
/// fact, that `result_var ∈ success` whenever the call's arguments are in
/// domain (`assert_domain_implies_membership` with `narrow_try`) — so it's
/// sound to unconditionally extract via the matching constructor's selector,
/// the same "assert the tester, then select" pattern `encode_proj` uses for
/// ordinary cross-kind union projections.
///
/// Returns `None` when extraction can't be resolved (constructor not found,
/// or a success arm's own sort can't be coerced into the combined success
/// sort) — the caller should report `Unknown`, never guess.
pub(crate) fn extract_success_value<'tm>(
    tm: &'tm TermManager,
    result_var: Term<'tm>,
    success: &SemExpr,
    distinct_preds: &SolverPreds<'tm>,
    name_defs: &NameDefs,
) -> Option<Term<'tm>> {
    // Not cross-kind at all: nothing to extract, result_var already IS the
    // success value (only possible if a future non-distinct-sort Fail
    // representation existed; kept as a defensive no-op, not a live path).
    if !result_var.sort().is_dt() {
        return Some(result_var);
    }
    let dt = result_var.sort().datatype();
    let target_sort = set_sort(tm, success, distinct_preds, name_defs)?;

    let mut extracted: Vec<(Term<'tm>, Term<'tm>)> = Vec::new();
    for arm in flatten_any_union(success) {
        let ctor_name = arm_ctor_name_for_arm(arm, distinct_preds);
        let ctor = (0..dt.num_constructors())
            .map(|i| dt.constructor(i))
            .find(|c| c.name() == ctor_name)?;
        let tester = tm.mk_term(Kind::ApplyTester, &[ctor.tester_term(), result_var.clone()]);
        let value = tm.mk_term(
            Kind::ApplySelector,
            &[ctor.selector(0).term(), result_var.clone()],
        );
        let value = if value.sort() == target_sort {
            value
        } else if target_sort.is_dt() && !target_sort.is_tuple() {
            coerce_to_union_dt(tm, value, &target_sort).ok()?
        } else {
            return None;
        };
        extracted.push((tester, value));
    }

    let (_, last_value) = extracted.pop()?;
    Some(
        extracted
            .into_iter()
            .rev()
            .fold(last_value, |acc, (tester, value)| {
                tm.mk_term(Kind::Ite, &[tester, value, acc])
            }),
    )
}

/// True if the range is *directly* a product set (not wrapped in any union).
///
/// A range that is a union — whether or not one arm is `Fail`/`Fail * Y` — has
/// no single arm that defines "the" product structure, so it's handled by the
/// general cross-kind datatype machinery in `set_sort` instead (the same as
/// any other multi-arm union, e.g. `(Nat * Nat) | Nat`). `Fail` no longer
/// needs special-casing here: it's a builtin distinct sort like any other, so
/// a `Fail`/`Fail * Y` arm is just another datatype arm, not a shape this
/// function needs to see through.
pub(crate) fn is_product_range(range: &SemExpr) -> bool {
    matches!(range.kind, SemExprKind::CartesianProduct(..))
}
