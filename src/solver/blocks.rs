//! Block/statement encoding and require/assert checking.

use std::collections::{HashMap, HashSet};

use cvc5::{Kind, Solver, Sort, Term, TermManager};

use crate::{
    kind::Kind as ValKind,
    semantics::tree::{SemExpr, SemExprKind, SemStmt, collect_loop_modified},
    span::{Span, Symbol},
};

use super::CheckResult;
use super::NameDefs;
use super::encode::{
    EncodeCtx, Env, coerce_to_sequence, encode_expr, integer_value, proj_from_tuple, tuple_arity,
};
use super::loops::{LoopCtx, check_for_inductive_step, check_inductive_step};
use super::membership::{Membership, SolverPreds, membership_constraint};
use super::obligations::BuiltinObligation;
use super::sort::set_sort;

/// The full `Seq(elem)` sort for a `let`/`mut` binding's declared `X*`
/// constraint, used by `coerce_to_sequence` to convert an array-literal
/// (tuple-sorted) RHS into a real `Seq` term — including, for a nested vector
/// like `Nat**`, recursively coercing each element. Returns `None` when the
/// constraint's sort can't be determined (propagates to `coerce_to_sequence`'s
/// integer fallback for the `[]` case).
fn declared_vector_seq_sort<'tm>(
    tm: &'tm TermManager,
    constraint: &SemExpr,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Option<Sort<'tm>> {
    set_sort(tm, constraint, distinct_preds, name_defs).filter(|s| s.is_sequence())
}

// ── Loop predicate ────────────────────────────────────────────────────────────

/// Returns `true` when any while or for-in loop in `stmts` modifies a variable
/// that carries no effective SMT constraint.
///
/// When this returns false every loop-modified variable has an inductively-verified
/// binding constraint, so a SAT result from the post-loop check is a genuine
/// counterexample rather than a spurious one caused by a free SMT variable.
pub(crate) fn body_has_unconstrained_loop_var<'tm>(
    stmts: &[SemStmt],
    constraint_env: &HashMap<Symbol, SemExpr>,
    tm: &'tm TermManager,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> bool {
    stmts.iter().any(|s| match s {
        SemStmt::While { body, .. } | SemStmt::ForIn { body, .. } => {
            let modified = collect_loop_modified(body);
            modified.iter().any(|n| match constraint_env.get(n) {
                None => true,
                Some(constraint) => {
                    let dummy = tm.mk_integer(0);
                    matches!(
                        membership_constraint(tm, dummy, constraint, name_defs, distinct_preds),
                        Membership::Unconstrained
                    )
                }
            })
        }
        SemStmt::Block(inner) => {
            body_has_unconstrained_loop_var(inner, constraint_env, tm, name_defs, distinct_preds)
        }
        _ => false,
    })
}

/// Returns `true` if `stmts` contains a `return` anywhere, at any nesting
/// depth (including inside nested `{ }` blocks and further-nested loops).
///
/// `While`/`ForIn` bodies are never processed by `encode_block`'s own
/// statement loop — they go through the separate induction-based reasoning
/// in `loops.rs`, which has no notion of "this loop iteration might exit the
/// whole function early." A `return` inside a loop body is therefore invisible
/// to the top-level function-return value that gets checked, silently
/// dropping the early-exit value entirely — proving properties about
/// whatever comes *after* the loop, even though the function may never reach
/// that code at runtime. Used to gate loop encoding: a loop whose body
/// contains a `return` must report `Unknown` rather than risk this false
/// proof, until the induction machinery can account for early exits.
fn stmts_contain_return(stmts: &[SemStmt]) -> bool {
    stmts.iter().any(|s| match s {
        SemStmt::Return { .. } => true,
        SemStmt::Block(inner) => stmts_contain_return(inner),
        SemStmt::While { body, .. } | SemStmt::ForIn { body, .. } => stmts_contain_return(body),
        _ => false,
    })
}

// ── Block encoder ─────────────────────────────────────────────────────────────

/// Everything `encode_block` threads unchanged through a statement sequence,
/// beyond the `EncodeCtx` cluster it composes: SSA/param bookkeeping shared
/// with the enclosing function check, plus the mutable tracking
/// (`constraint_env`/`immutable_names`/`has_runtime_assert`/`overflow_checks`)
/// that a block's `let`/`assign`/loop statements update as they go.
pub(crate) struct BlockCtx<'a, 'tm> {
    pub(crate) encode: EncodeCtx<'a, 'tm>,
    pub(crate) ssa_counter: &'a mut usize,
    pub(crate) param_names: &'a [Symbol],
    pub(crate) param_terms: &'a [Term<'tm>],
    pub(crate) constraint_env: &'a mut HashMap<Symbol, SemExpr>,
    pub(crate) has_runtime_assert: &'a mut bool,
    pub(crate) immutable_names: &'a mut HashSet<Symbol>,
    // Decided (proved/not) overflow-check outcomes for `While`/`ForIn` loop
    // bodies, which run on their own isolated inductive-step solver and so
    // can't defer to `encode.overflow_obligs` (that vec is only decided once,
    // back in the enclosing `check_sig`/`check_block_sig`, against the
    // *outer* solver) — `check_inductive_step`/`check_for_inductive_step`
    // decide and write directly into this map instead.
    pub(crate) overflow_checks: &'a mut HashMap<Span, bool>,
    /// Same rationale as `overflow_checks`, for int-soundness-plan phase 2's
    /// overload call-resolution side-channel.
    pub(crate) overload_resolutions: &'a mut HashMap<Span, Option<usize>>,
    /// Threaded to every `check_require`/loop-inductive-step solver this block
    /// (or a loop nested inside it) constructs, so `--timeout` actually bounds
    /// them — see the review note on `check_require`'s previously-missing
    /// `tlimit`.
    pub(crate) timeout_ms: u64,
}

/// Process a sequence of statements, threading the SSA environment.
///
/// Returns `Ok(Some(term))` where `term` is the last `SemStmt::Expr` value,
/// `Ok(None)` if there was no return expression, or `Err(result)` for an
/// early exit (require failure, unsupported construct, etc.).
///
/// `result_sort`: expected sort for the block's result expression.  Passed to
/// `encode_expr` for `SemStmt::Expr` so cross-kind union if/else bodies can
/// be coerced.
pub(crate) fn encode_block<'tm>(
    stmts: &[SemStmt],
    env: &mut Env<'tm>,
    ctx: &mut BlockCtx<'_, 'tm>,
    result_sort: Option<Sort<'tm>>,
) -> Result<Option<Term<'tm>>, CheckResult> {
    let top_guard = ctx.encode.tm.mk_boolean(true);
    let mut last_expr: Option<Term<'tm>> = None;

    for stmt in stmts {
        last_expr = None; // only the last Expr stmt is the return value
        match stmt {
            SemStmt::Let {
                name,
                constraint,
                value: _,
                ..
            } if matches!(constraint.kind_of, ValKind::Set(_)) => {
                // Immutable runtime set: opaque integer (heap pointer), no value encoding.
                let fresh_name = format!("{}_{}", name.0, ctx.ssa_counter);
                *ctx.ssa_counter += 1;
                let fresh = ctx
                    .encode
                    .tm
                    .mk_const(ctx.encode.tm.integer_sort(), &fresh_name);
                ctx.immutable_names.insert(name.clone());
                env.insert(name.clone(), fresh);
            }

            SemStmt::Let {
                name,
                constraint,
                value,
                ..
            } => {
                let val = encode_expr(value, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;
                // Local `X*` bindings: an array-literal RHS encodes as a tuple —
                // coerce to a genuine `Seq` term so `++`/`len`/indexing/reassignment
                // all see a real sequence-sorted value, matching how X*-kind
                // function parameters are already encoded.
                let val = if matches!(constraint.kind_of, ValKind::Vector(_)) {
                    let seq_sort = declared_vector_seq_sort(
                        ctx.encode.tm,
                        constraint,
                        ctx.encode.name_defs,
                        ctx.encode.distinct_preds,
                    );
                    coerce_to_sequence(ctx.encode.tm, val, seq_sort)
                        .map_err(CheckResult::Unknown)?
                } else {
                    val
                };
                let ssa_name = format!("{}_{}", name.0, ctx.ssa_counter);
                *ctx.ssa_counter += 1;
                // The fresh SSA constant must carry the value's own sort —
                // a hardcoded integer sort makes `Equal` ill-sorted for Bool
                // and tuple bindings, which aborts cvc5 outright.
                let fresh = ctx.encode.tm.mk_const(val.sort(), &ssa_name);
                let eq = ctx.encode.tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                ctx.encode.solver.assert_formula(eq.clone());
                // Deferred to the function-exit check (rather than checked here via
                // check_require) simply to keep this statement's handling uniform
                // with the other binder forms below — check_require itself is sound
                // either way since it now reads facts straight from `solver`.
                if let Membership::Constrained(c) = membership_constraint(
                    ctx.encode.tm,
                    fresh.clone(),
                    constraint,
                    ctx.encode.name_defs,
                    ctx.encode.distinct_preds,
                ) {
                    ctx.encode.builtin_obligs.push(BuiltinObligation {
                        path_cond: top_guard.clone(),
                        obligation: c,
                        violated_reason: format!(
                            "initial value of `{}` is not in `{}`",
                            name.0, constraint
                        ),
                    });
                }
                ctx.immutable_names.insert(name.clone());
                env.insert(name.clone(), fresh);
            }

            SemStmt::MutLet {
                name,
                constraint,
                value: _,
                ..
            } if matches!(constraint.kind_of, ValKind::Set(_)) => {
                // Runtime set values (Set(Int), Set(Bool)) can't be encoded in
                // QF_NIA. Represent the binding as an opaque integer (the heap
                // pointer) and skip the value encoding and membership assertion.
                let fresh_name = format!("{}_{}", name.0, ctx.ssa_counter);
                *ctx.ssa_counter += 1;
                let fresh = ctx
                    .encode
                    .tm
                    .mk_const(ctx.encode.tm.integer_sort(), &fresh_name);
                ctx.constraint_env.insert(name.clone(), constraint.clone());
                env.insert(name.clone(), fresh);
            }

            SemStmt::MutLet {
                name,
                constraint,
                value,
                ..
            } => {
                let val = encode_expr(value, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;
                // Same array-literal-to-sequence coercion as the `Let` case above.
                let val = if matches!(constraint.kind_of, ValKind::Vector(_)) {
                    let seq_sort = declared_vector_seq_sort(
                        ctx.encode.tm,
                        constraint,
                        ctx.encode.name_defs,
                        ctx.encode.distinct_preds,
                    );
                    coerce_to_sequence(ctx.encode.tm, val, seq_sort)
                        .map_err(CheckResult::Unknown)?
                } else {
                    val
                };
                let ssa_name = format!("{}_{}", name.0, ctx.ssa_counter);
                *ctx.ssa_counter += 1;
                // The fresh SSA constant must carry the value's own sort —
                // a hardcoded integer sort makes `Equal` ill-sorted for Bool
                // and tuple bindings, which aborts cvc5 outright.
                let fresh = ctx.encode.tm.mk_const(val.sort(), &ssa_name);
                let eq = ctx.encode.tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                ctx.encode.solver.assert_formula(eq.clone());
                // Deferred to the function-exit check — see the comment on the
                // `Let` case above.
                if let Membership::Constrained(c) = membership_constraint(
                    ctx.encode.tm,
                    fresh.clone(),
                    constraint,
                    ctx.encode.name_defs,
                    ctx.encode.distinct_preds,
                ) {
                    ctx.encode.builtin_obligs.push(BuiltinObligation {
                        path_cond: top_guard.clone(),
                        obligation: c,
                        violated_reason: format!(
                            "initial value of `{}` is not in `{}`",
                            name.0, constraint
                        ),
                    });
                }
                ctx.constraint_env.insert(name.clone(), constraint.clone());
                env.insert(name.clone(), fresh);
            }

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
                let is_mut = matches!(stmt, SemStmt::DestructMutLet { .. });

                let rhs_term = encode_expr(value, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;

                // Optional tuple-level constraint (e.g. `x, y : Int * Nat = ...`).
                // The parser currently always emits None; this path is future use.
                if let Some(tc) = tuple_constraint
                    && let Membership::Constrained(c) = membership_constraint(
                        ctx.encode.tm,
                        rhs_term.clone(),
                        tc,
                        ctx.encode.name_defs,
                        ctx.encode.distinct_preds,
                    )
                {
                    ctx.encode.builtin_obligs.push(BuiltinObligation {
                        path_cond: top_guard.clone(),
                        obligation: c,
                        violated_reason: format!("destructured value is not in `{}`", tc),
                    });
                }

                // Read arity from the tuple sort itself (not term children) — `rhs_term`
                // may be an opaque SSA constant (a local let-bound tuple variable), which
                // carries a genuine tuple sort but has no APPLY_CONSTRUCTOR children.
                let arity = tuple_arity(&rhs_term);
                let last_i = bindings.len() - 1;

                for (i, binding) in bindings.iter().enumerate() {
                    let is_tail = i == last_i && bindings.len() < arity;

                    if is_tail {
                        // Last binder collects remaining elements as a sub-tuple.
                        // ApplySelector (via proj_from_tuple) works on any tuple-sorted
                        // term, unlike `.child()` which requires a literal constructor
                        // application.
                        let tail: Vec<Term<'_>> = (i..arity)
                            .map(|j| proj_from_tuple(ctx.encode.tm, rhs_term.clone(), j))
                            .collect::<Result<_, _>>()
                            .map_err(CheckResult::Unknown)?;
                        let sub_tuple = ctx.encode.tm.mk_tuple(&tail);
                        if let Some(constraint) = &binding.constraint
                            && let Membership::Constrained(c) = membership_constraint(
                                ctx.encode.tm,
                                sub_tuple.clone(),
                                constraint,
                                ctx.encode.name_defs,
                                ctx.encode.distinct_preds,
                            )
                        {
                            ctx.encode.builtin_obligs.push(BuiltinObligation {
                                path_cond: top_guard.clone(),
                                obligation: c,
                                violated_reason: format!(
                                    "destructured tail `{}` is not in `{}`",
                                    binding.name.0, constraint
                                ),
                            });
                        }
                        if is_mut {
                            if let Some(constraint) = &binding.constraint {
                                ctx.constraint_env
                                    .insert(binding.name.clone(), constraint.clone());
                            }
                        } else {
                            ctx.immutable_names.insert(binding.name.clone());
                        }
                        env.insert(binding.name.clone(), sub_tuple);
                    } else {
                        let proj = proj_from_tuple(ctx.encode.tm, rhs_term.clone(), i)
                            .map_err(CheckResult::Unknown)?;
                        let ssa_name = format!("{}_{}", binding.name.0, ctx.ssa_counter);
                        *ctx.ssa_counter += 1;
                        let fresh = ctx.encode.tm.mk_const(proj.sort(), &ssa_name);
                        let eq = ctx.encode.tm.mk_term(Kind::Equal, &[fresh.clone(), proj]);
                        ctx.encode.solver.assert_formula(eq.clone());

                        if let Some(constraint) = &binding.constraint
                            && let Membership::Constrained(c) = membership_constraint(
                                ctx.encode.tm,
                                fresh.clone(),
                                constraint,
                                ctx.encode.name_defs,
                                ctx.encode.distinct_preds,
                            )
                        {
                            ctx.encode.builtin_obligs.push(BuiltinObligation {
                                path_cond: top_guard.clone(),
                                obligation: c,
                                violated_reason: format!(
                                    "destructured element {} (`{}`) is not in `{}`",
                                    i, binding.name.0, constraint
                                ),
                            });
                        }

                        if is_mut {
                            if let Some(constraint) = &binding.constraint {
                                ctx.constraint_env
                                    .insert(binding.name.clone(), constraint.clone());
                            }
                        } else {
                            ctx.immutable_names.insert(binding.name.clone());
                        }
                        env.insert(binding.name.clone(), fresh);
                    }
                }
            }

            SemStmt::DestructAssign {
                names: dest_names,
                value,
                ..
            } => {
                for name in dest_names.iter() {
                    if ctx.immutable_names.contains(name) {
                        return Err(CheckResult::Counterexample {
                            params: HashMap::new(),
                            output: 0,
                            reason: format!(
                                "cannot assign to `{}`: declared as an immutable binding \
                                 (use `mut {}` to allow reassignment)",
                                name.0, name.0
                            ),
                        });
                    }
                    if !env.contains_key(name) {
                        return Err(CheckResult::Unknown(format!(
                            "unbound variable `{}` in destructuring assignment",
                            name.0
                        )));
                    }
                }

                let rhs_term = encode_expr(value, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;

                // `DestructAssign` only understands a tuple-shaped RHS (the same
                // limitation as `DestructLet`/`DestructMutLet` — see the matching
                // guard in `elaborate_destruct_bindings`). Elaboration doesn't gate
                // this statement form at all (`:=` reuses names' existing Kind
                // rather than computing new ones), so a vector RHS (an opaque
                // integer term in the solver) would otherwise reach `child()` with
                // zero children and abort cvc5 outright.
                if !rhs_term.sort().is_tuple() {
                    return Err(CheckResult::Unknown(
                        "destructuring assignment (`:=`) only supports a tuple \
                         right-hand side (a vector `X*` right-hand side is not \
                         yet implemented)"
                            .into(),
                    ));
                }

                // Read arity from the tuple sort itself (not term children) — `rhs_term`
                // may be an opaque SSA constant (a local let-bound tuple variable), which
                // carries a genuine tuple sort but has no APPLY_CONSTRUCTOR children.
                let arity = tuple_arity(&rhs_term);
                let last_i = dest_names.len() - 1;

                for (i, name) in dest_names.iter().enumerate() {
                    let is_tail = i == last_i && dest_names.len() < arity;

                    if is_tail {
                        // Last binder collects remaining elements as a sub-tuple.
                        // ApplySelector (via proj_from_tuple) works on any tuple-sorted
                        // term, unlike `.child()` which requires a literal constructor
                        // application.
                        let tail: Vec<Term<'_>> = (i..arity)
                            .map(|j| proj_from_tuple(ctx.encode.tm, rhs_term.clone(), j))
                            .collect::<Result<_, _>>()
                            .map_err(CheckResult::Unknown)?;
                        let sub_tuple = ctx.encode.tm.mk_tuple(&tail);
                        if let Some(constraint) = ctx.constraint_env.get(name).cloned()
                            && let Membership::Constrained(c) = membership_constraint(
                                ctx.encode.tm,
                                sub_tuple.clone(),
                                &constraint,
                                ctx.encode.name_defs,
                                ctx.encode.distinct_preds,
                            )
                        {
                            match check_require(
                                c.clone(),
                                ctx.encode.tm,
                                ctx.encode.solver,
                                ctx.param_names,
                                ctx.param_terms,
                                ctx.timeout_ms,
                            ) {
                                CheckResult::Proved => {
                                    ctx.encode.solver.assert_formula(c.clone());
                                }
                                CheckResult::Counterexample { params, output, .. } => {
                                    return Err(CheckResult::Counterexample {
                                        params,
                                        output,
                                        reason: format!(
                                            "`{} :=` (destructured tail) violates declared constraint `{}`",
                                            name.0, constraint
                                        ),
                                    });
                                }
                                CheckResult::Unknown(msg) => {
                                    return Err(CheckResult::Unknown(msg));
                                }
                            }
                        }
                        env.insert(name.clone(), sub_tuple);
                    } else {
                        let proj = proj_from_tuple(ctx.encode.tm, rhs_term.clone(), i)
                            .map_err(CheckResult::Unknown)?;
                        let ssa_name = format!("{}_{}", name.0, ctx.ssa_counter);
                        *ctx.ssa_counter += 1;
                        let fresh = ctx.encode.tm.mk_const(proj.sort(), &ssa_name);
                        let eq = ctx.encode.tm.mk_term(Kind::Equal, &[fresh.clone(), proj]);
                        ctx.encode.solver.assert_formula(eq.clone());

                        if let Some(constraint) = ctx.constraint_env.get(name).cloned()
                            && let Membership::Constrained(c) = membership_constraint(
                                ctx.encode.tm,
                                fresh.clone(),
                                &constraint,
                                ctx.encode.name_defs,
                                ctx.encode.distinct_preds,
                            )
                        {
                            match check_require(
                                c.clone(),
                                ctx.encode.tm,
                                ctx.encode.solver,
                                ctx.param_names,
                                ctx.param_terms,
                                ctx.timeout_ms,
                            ) {
                                CheckResult::Proved => {
                                    ctx.encode.solver.assert_formula(c.clone());
                                }
                                CheckResult::Counterexample { params, output, .. } => {
                                    return Err(CheckResult::Counterexample {
                                        params,
                                        output,
                                        reason: format!(
                                            "`{} :=` (destructured) violates declared constraint `{}`",
                                            name.0, constraint
                                        ),
                                    });
                                }
                                CheckResult::Unknown(msg) => {
                                    return Err(CheckResult::Unknown(msg));
                                }
                            }
                        }

                        env.insert(name.clone(), fresh);
                    }
                }
            }

            SemStmt::Assign { name, .. } if ctx.immutable_names.contains(name) => {
                return Err(CheckResult::Counterexample {
                    params: HashMap::new(),
                    output: 0,
                    reason: format!(
                        "cannot assign to `{}`: declared as an immutable binding \
                         (use `mut {}` to allow reassignment)",
                        name.0, name.0
                    ),
                });
            }

            SemStmt::Assign { name, value, .. } => {
                let val = encode_expr(value, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;
                // Same array-literal-to-sequence coercion as `MutLet` — a bare
                // `xs := [1, 2, 3]` reassignment encodes as a tuple otherwise,
                // breaking the "X*-kind bindings are always Seq-sorted" invariant
                // that `++`/`len`/indexing/further `:=` depend on.
                let val = match ctx.constraint_env.get(name) {
                    Some(constraint) if matches!(constraint.kind_of, ValKind::Vector(_)) => {
                        let seq_sort = declared_vector_seq_sort(
                            ctx.encode.tm,
                            constraint,
                            ctx.encode.name_defs,
                            ctx.encode.distinct_preds,
                        );
                        coerce_to_sequence(ctx.encode.tm, val, seq_sort)
                            .map_err(CheckResult::Unknown)?
                    }
                    _ => val,
                };
                let ssa_name = format!("{}_{}", name.0, ctx.ssa_counter);
                *ctx.ssa_counter += 1;
                // The fresh SSA constant must carry the value's own sort —
                // a hardcoded integer sort makes `Equal` ill-sorted for Bool
                // and tuple bindings, which aborts cvc5 outright.
                let fresh = ctx.encode.tm.mk_const(val.sort(), &ssa_name);
                let eq = ctx.encode.tm.mk_term(Kind::Equal, &[fresh.clone(), val]);
                ctx.encode.solver.assert_formula(eq.clone());
                // Verify (not just trust) that the new value satisfies the declared
                // constraint. Inside loop bodies constraint_env is empty — the
                // inductive step checker handles loop invariants separately — so
                // this check only fires for non-loop reassignments.
                if let Some(constraint) = ctx.constraint_env.get(name).cloned()
                    && let Membership::Constrained(c) = membership_constraint(
                        ctx.encode.tm,
                        fresh.clone(),
                        &constraint,
                        ctx.encode.name_defs,
                        ctx.encode.distinct_preds,
                    )
                {
                    match check_require(
                        c.clone(),
                        ctx.encode.tm,
                        ctx.encode.solver,
                        ctx.param_names,
                        ctx.param_terms,
                        ctx.timeout_ms,
                    ) {
                        CheckResult::Proved => {
                            ctx.encode.solver.assert_formula(c.clone());
                        }
                        CheckResult::Counterexample { params, output, .. } => {
                            return Err(CheckResult::Counterexample {
                                params,
                                output,
                                reason: format!(
                                    "`{} :=` violates declared constraint `{}`",
                                    name.0, constraint
                                ),
                            });
                        }
                        CheckResult::Unknown(msg) => return Err(CheckResult::Unknown(msg)),
                    }
                }
                env.insert(name.clone(), fresh);
            }

            SemStmt::Assume { predicate, .. } => {
                let pred = encode_expr(predicate, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;
                ctx.encode.solver.assert_formula(pred.clone());
            }

            SemStmt::Require { predicate, .. } => {
                let pred = encode_expr(predicate, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;

                match check_require(
                    pred.clone(),
                    ctx.encode.tm,
                    ctx.encode.solver,
                    ctx.param_names,
                    ctx.param_terms,
                    ctx.timeout_ms,
                ) {
                    CheckResult::Proved => {
                        ctx.encode.solver.assert_formula(pred.clone());
                    }
                    other => return Err(other),
                }
            }

            SemStmt::Assert { predicate, .. } => {
                let pred = encode_expr(predicate, env, &mut ctx.encode, top_guard.clone(), None)
                    .map_err(CheckResult::Unknown)?;

                match check_require(
                    pred.clone(),
                    ctx.encode.tm,
                    ctx.encode.solver,
                    ctx.param_names,
                    ctx.param_terms,
                    ctx.timeout_ms,
                ) {
                    CheckResult::Proved => {
                        // Statically proved — no runtime check needed.
                        ctx.encode.solver.assert_formula(pred.clone());
                    }
                    CheckResult::Counterexample { params, output, .. } => {
                        // pred is not always true.  Check whether NOT(pred) is always
                        // true — if so, pred never holds → compile error.
                        // Otherwise pred is sometimes true → runtime check needed.
                        let not_pred = ctx
                            .encode
                            .tm
                            .mk_term(Kind::Not, std::slice::from_ref(&pred));
                        match check_require(
                            not_pred,
                            ctx.encode.tm,
                            ctx.encode.solver,
                            ctx.param_names,
                            ctx.param_terms,
                            ctx.timeout_ms,
                        ) {
                            CheckResult::Proved => {
                                return Err(CheckResult::Counterexample {
                                    params,
                                    output,
                                    reason: "assertion always fails".to_string(),
                                });
                            }
                            _ => {
                                // pred is sometimes true — codegen emits a runtime check.
                                *ctx.has_runtime_assert = true;
                                ctx.encode.solver.assert_formula(pred.clone());
                            }
                        }
                    }
                    CheckResult::Unknown(_) => {
                        *ctx.has_runtime_assert = true;
                        ctx.encode.solver.assert_formula(pred.clone());
                    }
                }
            }

            SemStmt::Return { value, .. } => {
                // `return` exits the function immediately — everything after it
                // in this statement sequence is unreachable, exactly like
                // codegen's `compile_return_stmt` (which emits a real `ret` and
                // never compiles what follows into a live block). The current
                // grammar has no statement-level branching in a flat `stmts`
                // sequence (`if` is value-position only; `while`/`for` bodies are
                // handled by the separate induction path in `loops.rs`, never by
                // this function), so a `return` reached here is unconditionally
                // reached — returning right away is sound, not an approximation.
                let t = encode_expr(
                    value,
                    env,
                    &mut ctx.encode,
                    top_guard.clone(),
                    result_sort.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                return Ok(Some(t));
            }

            SemStmt::Expr(e) => {
                let t = encode_expr(
                    e,
                    env,
                    &mut ctx.encode,
                    top_guard.clone(),
                    result_sort.clone(),
                )
                .map_err(CheckResult::Unknown)?;
                last_expr = Some(t);
            }

            SemStmt::Block(inner) => {
                last_expr = encode_block(inner, env, ctx, result_sort.clone())?;
            }

            SemStmt::While { cond, body, .. } => {
                if stmts_contain_return(body) {
                    return Err(CheckResult::Unknown(
                        "early `return` inside a `while` loop body is not yet \
                         supported in the SMT block encoder"
                            .into(),
                    ));
                }
                let modified = collect_loop_modified(body);
                let mut loop_ctx = LoopCtx {
                    constraint_env: ctx.constraint_env,
                    name_defs: ctx.encode.name_defs,
                    fn_env: ctx.encode.fn_env,
                    tm: ctx.encode.tm,
                    outer_solver: ctx.encode.solver,
                    ssa_counter: ctx.ssa_counter,
                    param_names: ctx.param_names,
                    param_terms: ctx.param_terms,
                    immutable_names: ctx.immutable_names,
                    distinct_preds: ctx.encode.distinct_preds,
                    has_runtime_assert: ctx.has_runtime_assert,
                    overflow_checks: ctx.overflow_checks,
                    overload_resolutions: ctx.overload_resolutions,
                    timeout_ms: ctx.timeout_ms,
                };
                if let Some(step_err) =
                    check_inductive_step(cond, body, &modified, env, &mut loop_ctx)
                {
                    return Err(step_err);
                }

                // Post-loop approximation: replace each loop-modified variable with
                // a fresh constant carrying its declared invariant (justified by the
                // proved inductive step), then assert ¬cond (loop has exited).
                // Immutable names cannot be modified in the loop body; if they appear
                // in `modified` it is a bug that the inductive step check already
                // reported — skip them here.
                for name in &modified {
                    if ctx.immutable_names.contains(name) {
                        continue;
                    }
                    if let Some(cur_sort) = env.get(name).map(|t| t.sort()) {
                        let fresh_name = format!("{}_{}", name.0, ctx.ssa_counter);
                        *ctx.ssa_counter += 1;
                        let fresh = ctx.encode.tm.mk_const(cur_sort, &fresh_name);
                        if let Some(constraint) = ctx.constraint_env.get(name)
                            && let Membership::Constrained(c) = membership_constraint(
                                ctx.encode.tm,
                                fresh.clone(),
                                constraint,
                                ctx.encode.name_defs,
                                ctx.encode.distinct_preds,
                            )
                        {
                            ctx.encode.solver.assert_formula(c.clone());
                        }
                        env.insert(name.clone(), fresh);
                    }
                }

                if let Ok(cond_term) =
                    encode_expr(cond, env, &mut ctx.encode, top_guard.clone(), None)
                {
                    // cond uses unsupported constructs — skip the fact (Err case)
                    let not_cond = ctx.encode.tm.mk_term(Kind::Not, &[cond_term]);
                    ctx.encode.solver.assert_formula(not_cond.clone());
                }

                last_expr = None;
            }

            SemStmt::ForIn { var, set, body, .. } => {
                // Empty set literal: body never executes, vars are unchanged.
                let is_empty_lit = matches!(&set.kind, SemExprKind::SetLit(e) if e.is_empty());
                if is_empty_lit {
                    last_expr = None;
                    continue;
                }
                if stmts_contain_return(body) {
                    return Err(CheckResult::Unknown(
                        "early `return` inside a `for` loop body is not yet \
                         supported in the SMT block encoder"
                            .into(),
                    ));
                }

                let modified = collect_loop_modified(body);
                let mut loop_ctx = LoopCtx {
                    constraint_env: ctx.constraint_env,
                    name_defs: ctx.encode.name_defs,
                    fn_env: ctx.encode.fn_env,
                    tm: ctx.encode.tm,
                    outer_solver: ctx.encode.solver,
                    ssa_counter: ctx.ssa_counter,
                    param_names: ctx.param_names,
                    param_terms: ctx.param_terms,
                    immutable_names: ctx.immutable_names,
                    distinct_preds: ctx.encode.distinct_preds,
                    has_runtime_assert: ctx.has_runtime_assert,
                    overflow_checks: ctx.overflow_checks,
                    overload_resolutions: ctx.overload_resolutions,
                    timeout_ms: ctx.timeout_ms,
                };
                if let Some(step_err) =
                    check_for_inductive_step(var, set, body, &modified, env, &mut loop_ctx)
                {
                    return Err(step_err);
                }

                // Post-loop: replace each modified var with a fresh constant
                // carrying its declared invariant (justified by the proved step).
                for name in &modified {
                    if ctx.immutable_names.contains(name) {
                        continue;
                    }
                    if let Some(cur_sort) = env.get(name).map(|t| t.sort()) {
                        let fresh_name = format!("{}_{}", name.0, ctx.ssa_counter);
                        *ctx.ssa_counter += 1;
                        let fresh = ctx.encode.tm.mk_const(cur_sort, &fresh_name);
                        if let Some(constraint) = ctx.constraint_env.get(name)
                            && let Membership::Constrained(c) = membership_constraint(
                                ctx.encode.tm,
                                fresh.clone(),
                                constraint,
                                ctx.encode.name_defs,
                                ctx.encode.distinct_preds,
                            )
                        {
                            ctx.encode.solver.assert_formula(c.clone());
                        }
                        env.insert(name.clone(), fresh);
                    }
                }

                last_expr = None;
            }
        }
    }

    Ok(last_expr)
}

// ── Require / assert helper ───────────────────────────────────────────────────

/// Run a temporary solver query to check whether `obligation` is provable
/// under everything asserted on `solver` so far. Returns `Proved`, a
/// `Counterexample`, or `Unknown` — never silently passes an unverified claim.
///
/// Seeding from `solver.get_assertions()` (rather than a separately-threaded
/// fact list) is load-bearing: call contracts (`args ∈ A → result ∈ B`) are
/// asserted straight onto `solver` by `assert_call_contract` and were never
/// mirrored into any parallel fact vector, so a `require`/`assert` after a
/// call used to see none of the callee's contract and could report a spurious
/// counterexample.
pub(crate) fn check_require<'tm>(
    obligation: Term<'tm>,
    tm: &'tm TermManager,
    solver: &Solver<'tm>,
    param_names: &[Symbol],
    param_terms: &[Term<'tm>],
    timeout_ms: u64,
) -> CheckResult {
    let mut tmp = super::configured_solver(tm, timeout_ms);

    for fact in solver.get_assertions() {
        tmp.assert_formula(fact);
    }
    tmp.assert_formula(tm.mk_term(Kind::Not, &[obligation]));

    let sat = tmp.check_sat();
    if sat.is_unsat() {
        CheckResult::Proved
    } else if sat.is_sat() {
        let mut params = HashMap::new();
        for (name, term) in param_names.iter().zip(param_terms.iter()) {
            let val = tmp.get_value(term.clone());
            params.insert(name.0.clone(), integer_value(&val));
        }
        CheckResult::Counterexample {
            params,
            output: 0,
            reason: "requirement failed".to_string(),
        }
    } else {
        CheckResult::Unknown("could not verify requirement".to_string())
    }
}
