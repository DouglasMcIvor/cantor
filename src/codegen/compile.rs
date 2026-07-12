//! Whole-file compilation entry points: constant-folding, the two-pass
//! declare/compile driver, and the plain (non-JIT) IR-dump entry point.
//! `jit.rs`'s `compile_constrained`/`compile_file` are thin wrappers around
//! `compile_elaborated`/`compile_items` here.
//!
//! Split out of `mod.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — mirrors `trampoline.rs`'s
//! own split.

use std::collections::HashMap;

use inkwell::{context::Context, values::FunctionValue};

use crate::{
    ast::{BinOp, DefKind, Expr, ExprKind, Item, UnOp},
    error::CompileError,
    kind::Kind,
    semantics::{
        elaborate::elaborate,
        tree::{SemExpr, SemFunctionBody, SemItem},
    },
    span::{Span, Symbol},
};

use super::{Compiler, Env, OverloadEntry};

/// Evaluate a constant expression at compile time.
fn eval_const(expr: &Expr, known: &HashMap<Symbol, i64>) -> Result<i64, CompileError> {
    match &expr.kind {
        ExprKind::IntLit(n) => Ok(*n),
        ExprKind::Var(sym) => known.get(sym).copied().ok_or_else(|| {
            CompileError::ice(format!(
                "constant `{}` is undefined or not yet evaluated (constants must appear before use in file order)",
                sym.0
            ))
        }),
        ExprKind::UnOp { op: UnOp::Neg, expr: inner } => Ok(-eval_const(inner, known)?),
        ExprKind::BinOp { op, lhs, rhs } => {
            let l = eval_const(lhs, known)?;
            let r = eval_const(rhs, known)?;
            match op {
                BinOp::Add => Ok(l.wrapping_add(r)),
                BinOp::Sub => Ok(l.wrapping_sub(r)),
                BinOp::Mul => Ok(l.wrapping_mul(r)),
                BinOp::Div => {
                    if r == 0 {
                        Err(CompileError::ice("division by zero in constant expression"))
                    } else {
                        Ok(l / r)
                    }
                }
                _ => Err(CompileError::ice(
                    "only integer arithmetic is supported in constant expressions",
                )),
            }
        }
        _ => Err(CompileError::ice(
            "only integer arithmetic is supported in constant expressions",
        )),
    }
}

/// Find the declared `(FunctionValue, SemFunctionDef)` for a given name and
/// arity among `decls` — used by the MVP event loop (docs/design-
/// decisions.md §6) to pick out `main`'s two overloads (0-arity seed,
/// 2-arity step) by shape after they've been mangled apart by `declare_function`.
fn find_by_name_arity<'ctx, 'a>(
    decls: &[(
        FunctionValue<'ctx>,
        &'a crate::semantics::tree::SemFunctionDef,
    )],
    name: &str,
    arity: usize,
) -> Option<(
    FunctionValue<'ctx>,
    &'a crate::semantics::tree::SemFunctionDef,
)> {
    decls
        .iter()
        .copied()
        .find(|(_, def)| def.name.0 == name && def.params.len() == arity)
}

/// True when `(param_kinds, return_kind)` matches the MVP event loop's fixed
/// v0 shape `Char* * S -> Char* * S` (docs/design-decisions.md §6) — 2
/// params, first param `Char*`, 2-element tuple return whose first element
/// is also `Char*`. Kind-only: the (stronger) identifier-equality checks on
/// `S` already happened in `solver::event_loop::validate_event_loop_main`
/// before this function's `ConstrainedTree` could exist at all.
fn is_event_loop_step_shape(param_kinds: &[Kind], return_kind: &Kind) -> bool {
    let is_char_star = |k: &Kind| matches!(k, Kind::Vector(elem) if **elem == Kind::Char);
    param_kinds.len() == 2
        && is_char_star(&param_kinds[0])
        && matches!(return_kind, Kind::Tuple(elems) if elems.len() == 2 && is_char_star(&elems[0]))
}

/// Compile every function in `items` into a single JIT module.
/// Elaborates `items` up front, then delegates to `compile_elaborated`.
/// Both `compile_file` and `compile_to_ir` use this — they don't require a
/// proof, unlike `compile_constrained`.
pub(super) fn compile_items<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
) -> Result<Compiler<'ctx>, CompileError> {
    let sem_items = elaborate(items)?;
    compile_elaborated(ctx, items, &sem_items, HashMap::new(), None, HashMap::new())
}

/// Compile an already-elaborated file — the shared core of `compile_items`
/// and `compile_constrained`. Does a two-pass compilation (declarations →
/// bodies) into a `Compiler`.
///
/// Takes `items` *and* `sem_items` because pass 0 (constant-folding) below
/// deliberately walks the raw AST rather than the elaborated tree — see its
/// comment for why.
///
/// `overflow_checks`/`overflow_ctx` come from a verified `ConstrainedTree`
/// (`compile_constrained`) or are empty/`None` (`compile_items` — no solver
/// verification ran, so every arithmetic op is conservatively unproved).
/// `overload_resolution` is the same story for int-soundness-plan phase 2:
/// from a verified `ConstrainedTree`, or empty (every overloaded call falls
/// back to runtime dispatch).
pub(super) fn compile_elaborated<'ctx>(
    ctx: &'ctx Context,
    items: &[Item],
    sem_items: &[SemItem],
    overflow_checks: HashMap<Span, bool>,
    overflow_ctx: Option<(String, String)>,
    overload_resolution: HashMap<Span, usize>,
) -> Result<Compiler<'ctx>, CompileError> {
    let mut compiler = Compiler::new(ctx, "cantor");
    compiler.overflow_checks = overflow_checks;
    compiler.overflow_ctx = overflow_ctx;
    compiler.overload_resolution = overload_resolution;
    compiler.declare_runtime_functions();

    // Pass 0 — evaluate scalar constants and build a shared env of inlined values.
    // Set-definition NameDefs (e.g. `HTTPError = {400, 503}`) are silently skipped
    // here because they have no scalar value to inline into function bodies; they
    // are collected separately into `user_set_vals` below. This pass works from
    // the raw AST — it's pure constant-folding, not a Kind/position concern the
    // elaborator needs to disambiguate.
    let mut const_vals: HashMap<Symbol, i64> = HashMap::new();
    for item in items {
        if let Item::NameDef(def) = item
            && let Ok(val) = eval_const(&def.value, &const_vals)
        {
            const_vals.insert(def.name.clone(), val);
        }
    }

    // Collect integer-value lists for set-literal NameDefs so that
    // `compile_membership` and `compile_try` can reason about named error sets
    // (e.g. `HTTPError = {400, 503}`) at compile time.
    let mut user_set_vals: HashMap<String, Vec<i64>> = HashMap::new();
    for item in items {
        if let Item::NameDef(def) = item
            && let ExprKind::SetLit(elements) = &def.value.kind
        {
            let vals: Option<Vec<i64>> = elements
                .iter()
                .map(|e| match &e.kind {
                    ExprKind::IntLit(n) => Some(*n),
                    ExprKind::Var(sym) => const_vals.get(sym).copied(),
                    _ => None,
                })
                .collect();
            if let Some(v) = vals {
                user_set_vals.insert(def.name.0.clone(), v);
            }
        }
    }
    compiler.user_set_vals = user_set_vals;

    compiler.distinct_names = items
        .iter()
        .filter_map(|item| match item {
            Item::NameDef(def) if def.kind == DefKind::Distinct => Some(def.name.0.clone()),
            _ => None,
        })
        .collect();

    // int-soundness-plan phase 3 step 4b: a named scalar constant is always
    // genuinely `Kind::Int` (tagged) — it's inlined unchanged into every
    // function's env regardless of that function's own representation, so
    // it can't default to `Int64` the way a bare literal inside a
    // Step-A-promoted body can (`current_bare_int_kind`). Whatever consumes
    // it (arithmetic, a call boundary) already knows how to reconcile a
    // tagged value against a raw one.
    let mut const_env: Env<'ctx> = Env::new();
    for (sym, &val) in &const_vals {
        let llvm_val = compiler.compile_tagged_i64_const(val)?;
        const_env.insert(sym.clone(), (llvm_val.into(), Kind::Int));
    }

    // int-soundness-plan phase 2: how many `FunctionDef`s share each name —
    // a count of 1 (the overwhelming common case) keeps today's plain LLVM
    // name; more than 1 is an overload set, mangled below so `add_function`
    // is never called twice under the same name (LLVM would otherwise
    // silently rename the second and nothing would ever call it).
    let mut overload_counts: HashMap<Symbol, usize> = HashMap::new();
    for item in sem_items {
        if let SemItem::FunctionDef(def) = item {
            *overload_counts.entry(def.name.clone()).or_insert(0) += 1;
        }
    }

    // Pass 1 — declare all function signatures so forward calls resolve.
    // Param and return Kinds come from the elaborator's first-signature
    // computation; overloaded functions must agree on the Kind of each
    // position within a (name, arity) group (enforced during elaboration).
    let mut next_overload_index: HashMap<Symbol, usize> = HashMap::new();
    let decls: Vec<(FunctionValue<'ctx>, &crate::semantics::tree::SemFunctionDef)> = sem_items
        .iter()
        .filter_map(|item| match item {
            SemItem::FunctionDef(def) => {
                let is_overloaded = overload_counts[&def.name] > 1;
                let index = next_overload_index.entry(def.name.clone()).or_insert(0);
                let overload_index = *index;
                *index += 1;

                let llvm_name = if is_overloaded {
                    format!("{}__ov{overload_index}", def.name.0)
                } else {
                    def.name.0.clone()
                };

                let fn_val = compiler.declare_function(
                    &llvm_name,
                    &def.params,
                    &def.param_kinds,
                    def.return_kind.clone(),
                );
                // Record the range expression so `compile_try` can determine what
                // error values `?` should propagate for this callee.
                if let Some(sig) = def.sigs.first() {
                    compiler
                        .fn_ranges
                        .insert(llvm_name.clone(), sig.range.clone());
                    // Record per-parameter domain set expressions so `coerce_call_arg`
                    // can disambiguate which arm of a `+`-typed parameter a scalar
                    // call argument belongs to.
                    if let Ok(parts) = crate::semantics::tree::sem_param_set_exprs(
                        sig.domain.as_ref(),
                        def.params.len(),
                    ) {
                        let parts: Vec<SemExpr> = parts.into_iter().cloned().collect();
                        if is_overloaded {
                            compiler
                                .overload_dispatch
                                .entry(def.name.0.clone())
                                .or_default()
                                .push(OverloadEntry {
                                    mangled_name: llvm_name.clone(),
                                    arity: def.params.len(),
                                    domain_parts: parts.clone(),
                                });
                        }
                        compiler.fn_param_set_exprs.insert(llvm_name.clone(), parts);
                    } else if is_overloaded {
                        // Domain didn't decompose (arity mismatch shouldn't
                        // happen here since this is the def's own params
                        // count) — still register the candidate so dispatch
                        // knows about it, with an empty (always-Trivial)
                        // domain-parts list rather than dropping it silently.
                        compiler
                            .overload_dispatch
                            .entry(def.name.0.clone())
                            .or_default()
                            .push(OverloadEntry {
                                mangled_name: llvm_name.clone(),
                                arity: def.params.len(),
                                domain_parts: Vec::new(),
                            });
                    }
                }
                Some((fn_val, def))
            }
            // Compile-time-only proof obligation (like `require`) — no
            // codegen, no runtime representation, nothing to declare.
            SemItem::NameDef(_) | SemItem::EquivDecl { .. } => None,
        })
        .collect();

    // Pass 2 — compile bodies with constants available. Borrows `decls`
    // (both elements are `Copy`) rather than consuming it, so the MVP event
    // loop's trampoline emission below can still look functions up by name/
    // arity afterward without redoing the declare pass.
    for &(fn_val, def) in decls.iter() {
        let is_fallible = def
            .sigs
            .iter()
            .any(|s| crate::semantics::tree::range_contains_fail(&s.range));

        match &def.body {
            SemFunctionBody::Expr(e) => {
                compiler.compile_function_body(
                    fn_val,
                    &def.params,
                    &def.param_kinds,
                    e,
                    is_fallible,
                    &const_env,
                )?;
            }
            SemFunctionBody::Block(stmts) => {
                compiler.compile_block_body(
                    fn_val,
                    &def.params,
                    &def.param_kinds,
                    stmts,
                    is_fallible,
                    &const_env,
                )?;
            }
        }
    }

    // Emit trampolines for `main` depending on its return kind. Only reached
    // when plain `main` is unmangled, i.e. there's exactly one `main` — the
    // MVP event loop's 2-overload `main` (below) is mangled instead (an
    // overload set of size 2), so this block is naturally a no-op for it.
    if let Some(main_fn) = compiler.module.get_function("main") {
        let ret_kind = compiler
            .fn_return_kinds
            .get("main")
            .cloned()
            .unwrap_or(Kind::Int);
        match &ret_kind {
            // Fallible main: emit an i64-returning runner that converts {i1, i64} to flat i64.
            Kind::Tuple(elems) if elems.first() == Some(&Kind::Fail) => {
                compiler.emit_fallible_main_runner(main_fn)?;
            }
            // Regular tuple main: emit the existing ptr-buffer trampoline.
            Kind::Tuple(_) => {
                compiler.emit_into_trampoline(main_fn, &ret_kind, "cantor_main_into")?;
            }
            _ => {}
        }
    }

    // MVP IO event loop (docs/design-decisions.md §6): `main` overloaded as
    // a 2-arity `Char* * S -> Char* * S` step plus a 0-arity `main : -> S`
    // seed. Shape/identifier validity is already guaranteed here —
    // `compile_constrained` only ever runs on a `ConstrainedTree` that
    // `solver::event_loop::validate_event_loop_main` already accepted — so
    // this is a Kind-only re-scan to find the two mangled overloads, not a
    // repeat of that validation.
    if let Some((step_fn, step_def)) = find_by_name_arity(&decls, "main", 2)
        && is_event_loop_step_shape(&step_def.param_kinds, &step_def.return_kind)
    {
        let Kind::Tuple(out_elems) = &step_def.return_kind else {
            unreachable!("is_event_loop_step_shape already checked this is a 2-elem Tuple");
        };
        let event_kind = &step_def.param_kinds[0];
        let output_kind = &out_elems[0];
        let state_kind = &out_elems[1];

        let (seed_fn, _) = find_by_name_arity(&decls, "main", 0).ok_or_else(|| {
            CompileError::ice(
                "event-loop main missing its 0-arity seed overload — \
                 should have been rejected by validate_event_loop_main",
            )
        })?;
        compiler.emit_into_trampoline(seed_fn, state_kind, "cantor_initial_state")?;
        compiler.emit_event_loop_step(step_fn, event_kind, state_kind, output_kind)?;
    }

    Ok(compiler)
}

/// Compile a parsed file and return the LLVM IR as a string (no JIT).
///
/// Useful in tests to assert whether something was handled at compile time
/// (no runtime calls in the IR) or at runtime (runtime calls present).
pub fn compile_to_ir(ctx: &Context, items: &[Item]) -> Result<String, CompileError> {
    let compiler = compile_items(ctx, items)?;
    Ok(compiler.module().print_to_string().to_string())
}
