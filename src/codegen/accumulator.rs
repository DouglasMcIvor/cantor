//! Loop-accumulator detection — the analysis behind `codegen::loops`'s
//! O(1)-append lowering.
//!
//! `v := v ++ [x]` inside a loop is the idiomatic way to build a vector in
//! Cantor, and it is quadratic: `cantor_vec_concat_i64` copies the whole
//! vector and arena-allocates on every single append, so filling an N-element
//! vector costs O(N^2). Measured, that is 3.5ms at N=1000 and 47ms at
//! N=4000 — and it is what caps the demos' grid resolution, not wasm.
//!
//! The fix is to accumulate into a `cantor_vec_builder_*` (O(1) push) for the
//! duration of the loop nest and freeze it once on the way out.
//!
//! **Why this is sound.** The lowering never mutates the accumulator's
//! existing vector: it seeds a *fresh* builder from it
//! (`cantor_vec_builder_from_*`), appends into that, and produces a *new*
//! vector at loop exit. So an alias made before the loop (`w = v`) still
//! sees exactly what it saw before, and no escape analysis is needed. The
//! one thing that would break is a read of `v` *during* the loop, since for
//! that window `v`'s alloca holds the stale pre-loop value while the builder
//! holds the truth — which is precisely what [`find_accumulators`] rules
//! out.

use crate::error::CompileError;
use crate::kind::Kind;
use crate::semantics::tree::{SemExpr, SemExprKind, SemStmt};
use crate::span::Symbol;

use super::{Compiler, Env};

impl<'ctx> Compiler<'ctx> {
    /// Lower one `acc := acc ++ rhs` onto `builder_val`.
    ///
    /// `rhs` is coerced to a vector first (it is a one-element sequence
    /// literal in every idiomatic use, but may be a whole vector or a bare
    /// scalar via sequence unification) and then appended. Going through
    /// `coerce_value_to_vector` rather than pushing elements directly is
    /// deliberate: it reuses the *exact* per-element tag/extend conversions
    /// `compile_tuple_as_vector` applies, so this path cannot drift from the
    /// ordinary one.
    ///
    /// TODO: the common `acc ++ [x]` case still allocates a one-element Arrow
    /// array per iteration. It is O(1) rather than the O(n) it replaced, so
    /// the asymptotics are already fixed, but pushing the single element
    /// straight onto the builder would remove the allocation entirely.
    pub(super) fn compile_accumulator_append(
        &self,
        builder_val: inkwell::values::IntValue<'ctx>,
        elem_kind: &Kind,
        rhs: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let (val, kind) = self.compile_expr(rhs, env)?;
        let (vec_val, _) = self.coerce_value_to_vector(val, kind, elem_kind)?;
        let extend_fn = self
            .module
            .get_function(builder_extend_fn_name(elem_kind))
            .ok_or_else(|| CompileError::ice("vector builder-extend fn not declared"))?;
        self.builder
            .build_call(
                extend_fn,
                &[builder_val.into(), vec_val.into_int_value().into()],
                "acc_extend",
            )
            .map_err(|e| CompileError::ice(e.to_string()))?;
        Ok(())
    }
}

/// A `mut` vector variable a loop nest only ever extends.
pub(super) struct Accumulator {
    pub(super) name: Symbol,
    pub(super) elem_kind: Kind,
}

/// Runtime entry point building a builder pre-loaded from an existing vector.
/// Total over the element kinds [`find_accumulators`] admits.
pub(super) fn builder_from_fn_name(ek: &Kind) -> &'static str {
    match ek {
        Kind::Bool => "cantor_vec_builder_from_bool",
        _ => "cantor_vec_builder_from_i64",
    }
}

/// Runtime entry point appending a whole vector to a builder — the general
/// `acc := acc ++ rhs` case where `rhs` is not a literal.
pub(super) fn builder_extend_fn_name(ek: &Kind) -> &'static str {
    match ek {
        Kind::Bool => "cantor_vec_builder_extend_bool",
        _ => "cantor_vec_builder_extend_i64",
    }
}

/// The accumulators in `body` that can be lowered onto a builder.
///
/// An accumulator qualifies when, across the whole loop nest:
///   - there is exactly one assignment to it, and it has the shape
///     `name := name ++ rhs`;
///   - the name appears nowhere else at all — not in `cond`, not in a nested
///     loop's condition, not in `rhs`, not read by any other statement;
///   - the nest contains no `return` (an early exit would leave the builder
///     unfrozen; cheap to exclude and no real program in the tree does it).
///
/// `elem_kind_of` supplies the variable's Kind from the enclosing `Env`;
/// only element kinds with a builder ABI (`Int`-family and `Bool`) qualify.
pub(super) fn find_accumulators(
    cond: &SemExpr,
    body: &[SemStmt],
    elem_kind_of: impl Fn(&Symbol) -> Option<Kind>,
) -> Vec<Accumulator> {
    if stmts_contain_return(body) {
        return Vec::new();
    }

    let mut candidates: Vec<Symbol> = Vec::new();
    collect_candidates(body, &mut candidates);
    candidates.sort_by(|a, b| a.0.cmp(&b.0));
    candidates.dedup();

    candidates
        .into_iter()
        .filter_map(|name| {
            let elem_kind = match elem_kind_of(&name) {
                Some(Kind::Vector(elem)) => *elem,
                _ => return None,
            };
            if !matches!(elem_kind, Kind::Int | Kind::Int64 | Kind::Bool) {
                return None;
            }
            // One accumulate, and nothing else anywhere.
            if count_accumulates(body, &name) != 1 {
                return None;
            }
            if expr_mentions(cond, &name) || other_uses(body, &name) {
                return None;
            }
            Some(Accumulator { name, elem_kind })
        })
        .collect()
}

/// Every name assigned via the `name := name ++ rhs` shape, without yet
/// checking the "and nowhere else" conditions.
fn collect_candidates(stmts: &[SemStmt], out: &mut Vec<Symbol>) {
    for stmt in stmts {
        match stmt {
            SemStmt::Assign { name, value, .. } => {
                if accumulate_rhs(value, name).is_some() {
                    out.push(name.clone());
                }
            }
            SemStmt::While { body, .. } | SemStmt::ForIn { body, .. } => {
                collect_candidates(body, out)
            }
            SemStmt::Block(inner) => collect_candidates(inner, out),
            _ => {}
        }
    }
}

/// If `value` is `name ++ rhs`, the `rhs`. `name` appearing inside `rhs`
/// disqualifies it — that would read the accumulator mid-update.
pub(super) fn accumulate_rhs<'a>(value: &'a SemExpr, name: &Symbol) -> Option<&'a SemExpr> {
    let SemExprKind::BinOp {
        op: crate::ast::BinOp::Concat,
        lhs,
        rhs,
    } = &value.kind
    else {
        return None;
    };
    let SemExprKind::Var(v) = &lhs.kind else {
        return None;
    };
    if v != name || expr_mentions(rhs, name) {
        return None;
    }
    Some(rhs)
}

fn count_accumulates(stmts: &[SemStmt], name: &Symbol) -> usize {
    let mut n = 0;
    for stmt in stmts {
        match stmt {
            SemStmt::Assign {
                name: assigned,
                value,
                ..
            } => {
                if assigned == name && accumulate_rhs(value, name).is_some() {
                    n += 1;
                }
            }
            SemStmt::While { body, .. } | SemStmt::ForIn { body, .. } => {
                n += count_accumulates(body, name)
            }
            SemStmt::Block(inner) => n += count_accumulates(inner, name),
            _ => {}
        }
    }
    n
}

/// Any mention of `name` that is *not* the accumulate itself: a read in
/// another statement, a nested loop's condition, a rebinding, a destructure.
fn other_uses(stmts: &[SemStmt], name: &Symbol) -> bool {
    stmts.iter().any(|stmt| match stmt {
        SemStmt::Assign {
            name: assigned,
            value,
            ..
        } => {
            if assigned == name {
                // The accumulate reads `name` as the concat's lhs, which is
                // expected; anything else about this assignment is not.
                accumulate_rhs(value, name).is_none()
            } else {
                expr_mentions(value, name)
            }
        }
        SemStmt::Let {
            name: bound,
            constraint,
            value,
            ..
        }
        | SemStmt::MutLet {
            name: bound,
            constraint,
            value,
            ..
        } => bound == name || expr_mentions(constraint, name) || expr_mentions(value, name),
        SemStmt::DestructLet {
            bindings,
            tuple_constraint,
            value,
            ..
        }
        | SemStmt::DestructMutLet {
            bindings,
            tuple_constraint,
            value,
            ..
        } => {
            bindings.iter().any(|b| &b.name == name)
                || tuple_constraint
                    .as_ref()
                    .is_some_and(|c| expr_mentions(c, name))
                || expr_mentions(value, name)
        }
        SemStmt::DestructAssign { names, value, .. } => {
            names.contains(name) || expr_mentions(value, name)
        }
        SemStmt::Require { predicate, .. } | SemStmt::Assume { predicate, .. } => {
            expr_mentions(predicate, name)
        }
        SemStmt::Assert {
            predicate,
            else_clause,
            ..
        } => {
            expr_mentions(predicate, name)
                || else_clause
                    .as_ref()
                    .is_some_and(|e| assert_else_mentions(e, name))
        }
        SemStmt::Expr(e) => expr_mentions(e, name),
        SemStmt::Block(inner) => other_uses(inner, name),
        SemStmt::While { cond, body, .. } => expr_mentions(cond, name) || other_uses(body, name),
        SemStmt::ForIn { var, set, body, .. } => {
            var == name || expr_mentions(set, name) || other_uses(body, name)
        }
        // Conservatively treat anything this analysis has not been taught
        // about as a use, so a new `SemStmt` variant cannot silently opt into
        // the optimisation.
        _ => true,
    })
}

fn assert_else_mentions(clause: &crate::semantics::tree::SemAssertElse, name: &Symbol) -> bool {
    match clause {
        crate::semantics::tree::SemAssertElse::FailWith(e)
        | crate::semantics::tree::SemAssertElse::Return(e) => expr_mentions(e, name),
    }
}

/// Any early exit from the nest, including an `assert … else return`, leaves
/// the builder unfrozen. Cheap to exclude outright.
fn stmts_contain_return(stmts: &[SemStmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        SemStmt::Return { .. } => true,
        SemStmt::While { body, .. } | SemStmt::ForIn { body, .. } => stmts_contain_return(body),
        SemStmt::Block(inner) => stmts_contain_return(inner),
        SemStmt::Assert { else_clause, .. } => matches!(
            else_clause,
            Some(crate::semantics::tree::SemAssertElse::Return(_))
        ),
        _ => false,
    })
}

/// Whether `name` occurs anywhere in `expr`. Deliberately structural and
/// exhaustive-by-default: an unrecognised expression shape counts as a
/// mention, so the optimisation fails closed.
pub(super) fn expr_mentions(expr: &SemExpr, name: &Symbol) -> bool {
    let mut found = false;
    walk_expr(expr, &mut |e| {
        if let SemExprKind::Var(v) = &e.kind
            && v == name
        {
            found = true;
        }
    });
    found
}

/// Deliberately has no wildcard arm: adding a `SemExprKind` variant must be
/// a compile error here rather than a silently missed sub-expression, which
/// would let the optimisation fire on a loop that does read its accumulator.
fn walk_expr(expr: &SemExpr, f: &mut impl FnMut(&SemExpr)) {
    f(expr);
    match &expr.kind {
        SemExprKind::IntLit(_)
        | SemExprKind::BoolLit(_)
        | SemExprKind::CharLit(_)
        | SemExprKind::Var(_)
        | SemExprKind::FailLit
        | SemExprKind::NoneLit => {}
        SemExprKind::Add(l, r)
        | SemExprKind::DisjointUnion(l, r)
        | SemExprKind::Sub(l, r)
        | SemExprKind::SetDifference(l, r)
        | SemExprKind::Mul(l, r)
        | SemExprKind::CartesianProduct(l, r)
        | SemExprKind::Div(l, r)
        | SemExprKind::BinOp { lhs: l, rhs: r, .. }
        | SemExprKind::Index { base: l, index: r } => {
            walk_expr(l, f);
            walk_expr(r, f);
        }
        SemExprKind::SetQuotient(inner, _)
        | SemExprKind::UnOp { expr: inner, .. }
        | SemExprKind::Try(inner)
        | SemExprKind::FailWith(inner)
        | SemExprKind::Proj { base: inner, .. }
        | SemExprKind::KleeneStar(inner) => walk_expr(inner, f),
        SemExprKind::Call { args, .. } => args.iter().for_each(|a| walk_expr(a, f)),
        SemExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            walk_expr(cond, f);
            walk_expr(then_expr, f);
            walk_expr(else_expr, f);
        }
        SemExprKind::Tuple(elems) | SemExprKind::SetLit(elems) => {
            elems.iter().for_each(|e| walk_expr(e, f))
        }
        SemExprKind::Comprehension {
            output,
            source,
            filter,
            ..
        } => {
            walk_expr(output, f);
            walk_expr(source, f);
            if let Some(filter) = filter {
                walk_expr(filter, f);
            }
        }
    }
}
