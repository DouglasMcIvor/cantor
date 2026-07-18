//! Disjointness checking: the pre-existing `+` (disjoint union) operand
//! check, and int-soundness-plan phase 2's overload-domain disjointness
//! obligation — both reduce to the same "fresh solver + membership_constraint
//! + check_sat" shape.
//!
//! Split out of `mod.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — mirrors phase 1's own
//! `encode.rs` → `encode_call.rs` split.

use std::collections::HashMap;

use cvc5::{Kind, Term, TermManager};

use crate::kind::Kind as ValKind;
use crate::semantics::tree::{SemExpr, SemFunctionDef, sem_param_set_exprs};

use super::membership::{Membership, QuotientPreds, SolverPreds, membership_constraint};
use super::{
    CheckResult, FunctionEnv, NameDefs, boolean_value, build_distinct_preds, build_wrapping_preds,
    configured_solver, integer_value,
};

/// Verify that every `+` (disjoint union) in `set_expr` has genuinely disjoint operands.
///
/// Returns `Some(CheckResult)` on failure or `None` if all `+` nodes are proved disjoint.
/// Uses a fresh SMT solver per `+` node to avoid polluting the main check's solver state.
///
/// TODO: also validate `+` that appears inside function bodies (e.g. in `in` expressions).
pub(super) fn validate_disjoint_unions(
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
            let mut solver = configured_solver(&tm, timeout_ms);
            // No `fn_env` available in this auxiliary check (it's about
            // disjoint-union/overload-domain well-formedness, not general
            // membership), so quotient-set membership here safely degrades
            // to `Unsupported`/`Unknown` rather than being threaded through.
            let wrapping = build_wrapping_preds(&tm);
            let distinct = match build_distinct_preds(&tm, name_defs, &wrapping) {
                Ok(d) => d,
                Err(e) => return Some(CheckResult::Unknown(e)),
            };
            let distinct_preds = SolverPreds {
                distinct,
                wrapping,
                quotient: QuotientPreds::new(),
            };
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
        | SemExprKind::BinOp { lhs, rhs, .. } => {
            if let Some(err) = validate_disjoint_unions(lhs, name_defs, timeout_ms) {
                return Some(err);
            }
            validate_disjoint_unions(rhs, name_defs, timeout_ms)
        }
        // The RHS is a canonicalizer *function name*, not a set expression —
        // nothing to recurse into there.
        SemExprKind::SetQuotient(lhs, _canon) => {
            validate_disjoint_unions(lhs, name_defs, timeout_ms)
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
/// `domain_parts` is that one representative member's own declared domain,
/// split per position (`sem_param_set_exprs`) — needed (not just
/// `param_kinds`) to build a `TaggedUnion` position's fresh term at its
/// *actual* CVC5 sort (a distinct-set-specific algebraic datatype, not
/// something derivable from `Kind` alone, since two unrelated named unions
/// could share the same abstract `Kind::TaggedUnion(...)` shape). This is
/// sound *within* an overload group precisely because
/// `check_overload_kind_agreement` already guarantees every member's
/// declared param Kind matches exactly — constructor-pattern overloads of
/// one function always share the same declared union in practice (pattern-
/// matching plan step 4/4, `f(Shape.Circle(r)) = ...` / `f(Shape.Rect(p)) =
/// ...` both declare `f : Shape -> ...`).
///
/// TODO: `Tuple`/`Vector`/`Set` positions still return `Err` (reported as
/// `Unknown`), matching `validate_disjoint_unions`'s existing narrower
/// scope — only `Bool`/`Int`/`Int64`/`TaggedUnion` are lifted so far. Lift
/// the rest together if ever needed.
fn fresh_overload_param_terms<'tm>(
    param_kinds: &[ValKind],
    domain_parts: &[&SemExpr],
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Result<Vec<Term<'tm>>, String> {
    param_kinds
        .iter()
        .zip(domain_parts)
        .enumerate()
        .map(|(i, (kind, part))| match kind {
            ValKind::Bool => Ok(tm.mk_const(tm.boolean_sort(), &format!("__ov_disjoint_{i}"))),
            // Int64 reasons identically to Int here (int-soundness-plan
            // phase 3): the solver reasons over unbounded ℤ regardless of
            // raw-vs-tagged codegen representation, and the phase 3 split's
            // own Int64/BigInt overload pair needs this disjointness check
            // to work exactly like any other compiler-generated overload.
            ValKind::Int | ValKind::Int64 => {
                Ok(tm.mk_const(tm.integer_sort(), &format!("__ov_disjoint_{i}")))
            }
            ValKind::TaggedUnion(_) => {
                let sort = super::sort::set_sort(tm, part, distinct_preds, name_defs).ok_or_else(
                    || {
                        "cannot verify overload disjointness: this parameter's domain has no \
                         representable solver sort"
                            .to_string()
                    },
                )?;
                Ok(tm.mk_const(sort, &format!("__ov_disjoint_{i}")))
            }
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
    distinct_preds: &SolverPreds<'tm>,
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
    // No `fn_env` available here (an overload-domain-disjointness check, not
    // general membership) — quotient-set membership degrades to
    // `Unsupported`/`Unknown` rather than being threaded through.
    let wrapping = build_wrapping_preds(&tm);
    let distinct = match build_distinct_preds(&tm, name_defs, &wrapping) {
        Ok(d) => d,
        Err(e) => return CheckResult::Unknown(e),
    };
    let distinct_preds = SolverPreds {
        distinct,
        wrapping,
        quotient: QuotientPreds::new(),
    };

    let domain_parts = match sem_param_set_exprs(
        def_a.sigs.first().and_then(|s| s.domain.as_ref()),
        def_a.params.len(),
    ) {
        Ok(v) => v,
        Err(e) => return CheckResult::Unknown(e),
    };
    let param_terms = match fresh_overload_param_terms(
        &def_a.param_kinds,
        &domain_parts,
        &tm,
        name_defs,
        &distinct_preds,
    ) {
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

/// Pairwise-disjointness obligations for every (name, arity, parameter-Kind
/// bucket) group with more than one member in `fn_env` — groups of differing
/// arity need no check (arity alone is always statically decidable, so it
/// already makes them disjoint), and neither do groups of differing
/// parameter Kind (backlog.md "function overloads — support different
/// kinds": a `Bool` value and an `Int` value can never be equal, so two
/// overloads whose parameter Kinds genuinely differ are automatically
/// disjoint too — see `crate::semantics::elaborate::check_overload_kind_-
/// agreement`'s doc comment for why bucketing on parameter Kind alone is
/// always sound here).
pub(super) fn check_overload_disjointness(
    fn_env: &FunctionEnv<'_>,
    name_defs: &NameDefs,
    timeout_ms: u64,
) -> Vec<(String, Vec<(String, CheckResult)>)> {
    let mut out = Vec::new();
    for (name, defs) in fn_env {
        // Linear-scan grouping (not a `HashMap`) since `Kind` has no `Hash`
        // impl and overload sets are always small — mirrors
        // `elaborate::check_overload_kind_agreement`'s own bucketing.
        let bucket_key = |def: &SemFunctionDef| -> (usize, Vec<ValKind>) {
            (
                def.params.len(),
                def.param_kinds
                    .iter()
                    .map(crate::semantics::elaborate::canonical_bucket_kind)
                    .collect(),
            )
        };
        let mut groups: Vec<Vec<&SemFunctionDef>> = Vec::new();
        for def in defs {
            match groups
                .iter_mut()
                .find(|group| bucket_key(group[0]) == bucket_key(def))
            {
                Some(group) => group.push(*def),
                None => groups.push(vec![*def]),
            }
        }
        for group in &groups {
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
