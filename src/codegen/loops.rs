use std::collections::HashMap;

use inkwell::{
    IntPredicate,
    values::{BasicValueEnum, IntValue, PointerValue},
};

use crate::{
    error::CompileError,
    kind::{Kind, SetElemKind},
    semantics::tree::{SemExpr, SemExprKind, SemStmt, collect_loop_modified},
    span::Symbol,
};

use super::{Compiler, Env};

impl<'ctx> Compiler<'ctx> {
    /// Emit LLVM IR for `while cond { body }`.
    ///
    /// Variables assigned inside `body` that already exist in `env` are
    /// given alloca-backed storage so their values persist across iterations.
    /// New allocas are merged with any inherited from an outer loop so nested
    /// loops correctly write through to the outermost alloca.
    pub(super) fn compile_while(
        &mut self,
        cond: &SemExpr,
        body: &[SemStmt],
        env: &mut Env<'ctx>,
        outer_alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<(), CompileError> {
        let i64_type = self.context.i64_type();

        // Build the alloca map for this loop: start from the outer map (so
        // nested loops reuse the same allocas for shared variables) and add
        // new allocas for any body-modified variable not already covered.
        let modified = collect_loop_modified(body);
        let mut inner_alloca_map: HashMap<Symbol, PointerValue<'ctx>> = outer_alloca_map.clone();

        for name in &modified {
            if inner_alloca_map.contains_key(name) {
                continue; // already backed by an outer-loop alloca
            }
            if let Some(&(val, ref ty)) = env.get(name) {
                let ptr = self
                    .builder
                    .build_alloca(i64_type, &name.0)
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let val_i64: IntValue<'ctx> = if *ty == Kind::Bool {
                    self.builder
                        .build_int_z_extend(val.into_int_value(), i64_type, "bool_ext")
                        .map_err(|e| CompileError::ice(e.to_string()))?
                } else {
                    val.into_int_value()
                };
                self.builder
                    .build_store(ptr, val_i64)
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                inner_alloca_map.insert(name.clone(), ptr);
            }
        }

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("while loop outside a function"))?;

        let cond_bb = self.context.append_basic_block(function, "while_cond");
        let body_bb = self.context.append_basic_block(function, "while_body");
        let after_bb = self.context.append_basic_block(function, "while_after");

        self.builder
            .build_unconditional_branch(cond_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── Condition block ────────────────────────────────────────────────
        // Reload alloca'd variables so the condition sees the latest values.
        self.builder.position_at_end(cond_bb);
        let mut loop_env = env.clone();
        for (name, &ptr) in &inner_alloca_map {
            let val = self
                .builder
                .build_load(i64_type, ptr, &name.0)
                .map_err(|e| CompileError::ice(e.to_string()))?;
            let original_kind = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
            let entry = if original_kind == Kind::Bool {
                let i1 = self
                    .builder
                    .build_int_truncate(
                        val.into_int_value(),
                        self.context.bool_type(),
                        "reload_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                (i1.into(), Kind::Bool)
            } else {
                (val, original_kind)
            };
            loop_env.insert(name.clone(), entry);
        }
        let (cond_val, _) = self.compile_expr(cond, &loop_env)?;
        self.builder
            .build_conditional_branch(cond_val.into_int_value(), body_bb, after_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── Body block ─────────────────────────────────────────────────────
        self.builder.position_at_end(body_bb);
        let mut body_env = loop_env;
        self.compile_stmts(body, &mut body_env, &inner_alloca_map)?;
        self.builder
            .build_unconditional_branch(cond_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── After block ────────────────────────────────────────────────────
        // Reload the final alloca values back into the caller's env so
        // subsequent statements in the enclosing block see the results.
        self.builder.position_at_end(after_bb);
        for (name, &ptr) in &inner_alloca_map {
            let val = self
                .builder
                .build_load(i64_type, ptr, &format!("{}_final", name.0))
                .map_err(|e| CompileError::ice(e.to_string()))?;
            let original_kind = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
            let entry = if original_kind == Kind::Bool {
                let i1 = self
                    .builder
                    .build_int_truncate(
                        val.into_int_value(),
                        self.context.bool_type(),
                        "final_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                (i1.into(), Kind::Bool)
            } else {
                (val, original_kind)
            };
            env.insert(name.clone(), entry);
        }

        Ok(())
    }

    /// Emit LLVM IR for `for x in S { body }`.
    ///
    /// Supports set literals `{e1, e2, …}` and comprehensions `{out for v in {…} if pred}`
    /// as iterables.  Both are unrolled at compile time over their source elements.
    /// Named/generative sets need a runtime set representation that doesn't exist yet.
    pub(super) fn compile_for_in(
        &mut self,
        var: &Symbol,
        set: &SemExpr,
        body: &[SemStmt],
        env: &mut Env<'ctx>,
        alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<(), CompileError> {
        match &set.kind {
            SemExprKind::SetLit(elements) => {
                let i64_type = self.context.i64_type();
                for elem in elements {
                    let (elem_val, elem_ty) = self.compile_expr(elem, env)?;
                    let val_i64: BasicValueEnum = if elem_ty == Kind::Bool {
                        self.builder
                            .build_int_z_extend(elem_val.into_int_value(), i64_type, "bool_ext")
                            .map_err(|e| CompileError::ice(e.to_string()))?
                            .into()
                    } else {
                        elem_val
                    };
                    env.insert(var.clone(), (val_i64, Kind::Int));
                    self.compile_stmts(body, env, alloca_map)?;
                }
                Ok(())
            }
            SemExprKind::Comprehension {
                output,
                var: comp_var,
                source,
                filter,
            } => {
                let comp_var = comp_var.clone();
                let output = output.as_ref().clone();
                let source = source.as_ref().clone();
                let filter = filter.as_ref().map(|f| f.as_ref().clone());
                self.compile_for_in_comprehension(
                    var,
                    &output,
                    &comp_var,
                    &source,
                    filter.as_ref(),
                    body,
                    env,
                    alloca_map,
                )
            }
            _ => {
                // Compile the set expression and dispatch on its runtime Kind.
                let (ptr, kind) = self.compile_expr(set, env)?;
                match kind {
                    Kind::Set(elem_kind) => {
                        self.compile_for_in_runtime_set(var, ptr, elem_kind, body, env, alloca_map)
                    }
                    _ => Err(CompileError::ice(
                        "for loop: iterable must be a set literal, comprehension, \
                         or a variable of `Set(…)` kind",
                    )),
                }
            }
        }
    }

    /// Emit LLVM IR for `for var in <runtime-set> { body }`.
    ///
    /// Iterates 0..size, calling `cantor_set_get_*` each time to bind `var`.
    /// Body-modified variables are alloca-backed so their values survive across
    /// iterations — same strategy as `compile_while`.
    fn compile_for_in_runtime_set(
        &mut self,
        var: &Symbol,
        set_ptr: BasicValueEnum<'ctx>,
        elem_kind: SetElemKind,
        body: &[SemStmt],
        env: &mut Env<'ctx>,
        outer_alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<(), CompileError> {
        let i64t = self.context.i64_type();

        // Build alloca map for body-modified variables (same pattern as compile_while).
        let modified = collect_loop_modified(body);
        let mut inner_alloca_map: HashMap<Symbol, PointerValue<'ctx>> = outer_alloca_map.clone();
        for name in &modified {
            if inner_alloca_map.contains_key(name) {
                continue;
            }
            if let Some(&(val, ref ty)) = env.get(name) {
                let ptr = self
                    .builder
                    .build_alloca(i64t, &name.0)
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let val_i64: IntValue<'ctx> = if *ty == Kind::Bool {
                    self.builder
                        .build_int_z_extend(val.into_int_value(), i64t, "bool_ext")
                        .map_err(|e| CompileError::ice(e.to_string()))?
                } else {
                    val.into_int_value()
                };
                self.builder
                    .build_store(ptr, val_i64)
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                inner_alloca_map.insert(name.clone(), ptr);
            }
        }

        // Get set size once before the loop.
        let size_fn_name = match elem_kind {
            SetElemKind::Int => "cantor_set_size_i64",
            SetElemKind::Bool => "cantor_set_size_bool",
        };
        let size_fn = self
            .module
            .get_function(size_fn_name)
            .ok_or_else(|| CompileError::ice(format!("{size_fn_name} not declared")))?;
        let n = self
            .builder
            .build_call(size_fn, &[set_ptr.into()], "set_n")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("size fn returned void"))?
            .into_int_value();

        // Alloca for the loop counter.
        let i_ptr = self
            .builder
            .build_alloca(i64t, "set_i")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        self.builder
            .build_store(i_ptr, i64t.const_int(0, false))
            .map_err(|e| CompileError::ice(e.to_string()))?;

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("for-in loop outside a function"))?;

        let cond_bb = self.context.append_basic_block(function, "for_set_cond");
        let body_bb = self.context.append_basic_block(function, "for_set_body");
        let after_bb = self.context.append_basic_block(function, "for_set_after");

        self.builder
            .build_unconditional_branch(cond_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── Condition block: reload alloca vars, test i < n ────────────────────
        self.builder.position_at_end(cond_bb);
        let mut loop_env = env.clone();
        for (name, &ptr) in &inner_alloca_map {
            let val = self
                .builder
                .build_load(i64t, ptr, &name.0)
                .map_err(|e| CompileError::ice(e.to_string()))?;
            let original_kind = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
            let entry = if original_kind == Kind::Bool {
                let i1 = self
                    .builder
                    .build_int_truncate(
                        val.into_int_value(),
                        self.context.bool_type(),
                        "reload_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                (i1.into(), Kind::Bool)
            } else {
                (val, original_kind)
            };
            loop_env.insert(name.clone(), entry);
        }
        let i_val = self
            .builder
            .build_load(i64t, i_ptr, "i_val")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();
        let cond = self
            .builder
            .build_int_compare(IntPredicate::SLT, i_val, n, "for_cond")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        self.builder
            .build_conditional_branch(cond, body_bb, after_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── Body block: fetch element, bind var, compile body, increment i ──────
        self.builder.position_at_end(body_bb);
        let get_fn_name = match elem_kind {
            SetElemKind::Int => "cantor_set_get_i64",
            SetElemKind::Bool => "cantor_set_get_bool",
        };
        let get_fn = self
            .module
            .get_function(get_fn_name)
            .ok_or_else(|| CompileError::ice(format!("{get_fn_name} not declared")))?;
        let elem_raw = self
            .builder
            .build_call(get_fn, &[set_ptr.into(), i_val.into()], "elem_raw")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("get fn returned void"))?;
        let (elem_val, elem_k): (BasicValueEnum<'ctx>, Kind) = match elem_kind {
            SetElemKind::Int => (elem_raw, Kind::Int),
            SetElemKind::Bool => {
                let i1 = self
                    .builder
                    .build_int_truncate(
                        elem_raw.into_int_value(),
                        self.context.bool_type(),
                        "elem_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                (i1.into(), Kind::Bool)
            }
        };

        let mut body_env = loop_env;
        body_env.insert(var.clone(), (elem_val, elem_k));
        self.compile_stmts(body, &mut body_env, &inner_alloca_map)?;

        // Reload i from the alloca (safe after any inner loops the body may contain).
        let i_curr = self
            .builder
            .build_load(i64t, i_ptr, "i_curr")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();
        let i_next = self
            .builder
            .build_int_add(i_curr, i64t.const_int(1, false), "i_next")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        self.builder
            .build_store(i_ptr, i_next)
            .map_err(|e| CompileError::ice(e.to_string()))?;
        self.builder
            .build_unconditional_branch(cond_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── After block: propagate final alloca values back into caller's env ───
        self.builder.position_at_end(after_bb);
        for (name, &ptr) in &inner_alloca_map {
            let val = self
                .builder
                .build_load(i64t, ptr, &format!("{}_final", name.0))
                .map_err(|e| CompileError::ice(e.to_string()))?;
            let original_kind = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
            let entry = if original_kind == Kind::Bool {
                let i1 = self
                    .builder
                    .build_int_truncate(
                        val.into_int_value(),
                        self.context.bool_type(),
                        "final_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                (i1.into(), Kind::Bool)
            } else {
                (val, original_kind)
            };
            env.insert(name.clone(), entry);
        }

        Ok(())
    }

    /// Emit LLVM IR for `for var in { output for comp_var in source if filter } { body }`.
    ///
    /// Requires `source` to be a set literal.  For each source element, the comp_var
    /// is bound, the filter (if any) is evaluated, and — when the filter passes — the
    /// output expression is evaluated and bound to `var` before executing the body.
    ///
    /// When a filter is present, conditional branches create multiple control-flow
    /// paths.  Any variable modified in the body that is NOT backed by an outer-loop
    /// alloca is given a fresh alloca here so both paths (filter-true and filter-false)
    /// reload the correct value from memory rather than using a stale LLVM value from
    /// a non-dominating block.
    // TODO: 9 params is a clippy::too_many_arguments smell; consider bundling the
    // comprehension pieces (output/comp_var/source/filter) into a struct.
    #[allow(clippy::too_many_arguments)]
    fn compile_for_in_comprehension(
        &mut self,
        var: &Symbol,
        output: &SemExpr,
        comp_var: &Symbol,
        source: &SemExpr,
        filter: Option<&SemExpr>,
        body: &[SemStmt],
        env: &mut Env<'ctx>,
        outer_alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<(), CompileError> {
        let SemExprKind::SetLit(elements) = &source.kind else {
            return Err(CompileError::ice(
                "comprehension in `for` source: only set literal sources are supported \
                 in this version",
            ));
        };

        let i64_type = self.context.i64_type();
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("for-in comprehension outside a function"))?;

        // When a filter is present we use an alloca-backed map for all body-modified
        // variables so that both the taken and skipped paths through the conditional
        // branch see the same authoritative value after each element.  Mirrors the
        // alloca strategy in compile_while.
        let alloca_map: HashMap<Symbol, PointerValue<'ctx>> = if filter.is_some() {
            let modified = collect_loop_modified(body);
            let mut amap = outer_alloca_map.clone();
            for name in &modified {
                if amap.contains_key(name) {
                    continue;
                }
                if let Some(&(val, ref ty)) = env.get(name) {
                    let ptr = self
                        .builder
                        .build_alloca(i64_type, &name.0)
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let val_i64: IntValue<'ctx> = if *ty == Kind::Bool {
                        self.builder
                            .build_int_z_extend(val.into_int_value(), i64_type, "bool_ext")
                            .map_err(|e| CompileError::ice(e.to_string()))?
                    } else {
                        val.into_int_value()
                    };
                    self.builder
                        .build_store(ptr, val_i64)
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    amap.insert(name.clone(), ptr);
                }
            }
            amap
        } else {
            outer_alloca_map.clone()
        };

        for elem in elements {
            let (elem_val, elem_ty) = self.compile_expr(elem, env)?;
            // Bind the comprehension variable with its natural Kind.
            env.insert(comp_var.clone(), (elem_val, elem_ty));

            if let Some(filter_expr) = filter {
                // Reload alloca-backed values before the filter check so the condition
                // sees the post-previous-iteration value (not a stale env entry).
                for (name, &ptr) in &alloca_map {
                    if name == comp_var {
                        continue;
                    }
                    let val = self
                        .builder
                        .build_load(i64_type, ptr, &name.0)
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let k = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
                    let entry = if k == Kind::Bool {
                        let i1 = self
                            .builder
                            .build_int_truncate(
                                val.into_int_value(),
                                self.context.bool_type(),
                                "reload_bool",
                            )
                            .map_err(|e| CompileError::ice(e.to_string()))?;
                        (i1.into(), Kind::Bool)
                    } else {
                        (val, k)
                    };
                    env.insert(name.clone(), entry);
                }

                let (cond_val, _) = self.compile_expr(filter_expr, env)?;
                let cond_i1 = cond_val.into_int_value();

                let body_bb = self.context.append_basic_block(function, "comp_body");
                let next_bb = self.context.append_basic_block(function, "comp_next");

                self.builder
                    .build_conditional_branch(cond_i1, body_bb, next_bb)
                    .map_err(|e| CompileError::ice(e.to_string()))?;

                // ── Body (filter passed) ───────────────────────────────────────
                self.builder.position_at_end(body_bb);
                let (out_val, out_ty) = self.compile_expr(output, env)?;
                env.insert(var.clone(), (out_val, out_ty));
                self.compile_stmts(body, env, &alloca_map)?;
                self.builder
                    .build_unconditional_branch(next_bb)
                    .map_err(|e| CompileError::ice(e.to_string()))?;

                // ── After (both paths merge) ───────────────────────────────────
                // Reload from allocas: authoritative value regardless of which path
                // was taken.
                self.builder.position_at_end(next_bb);
                for (name, &ptr) in &alloca_map {
                    if name == comp_var {
                        continue;
                    }
                    let val = self
                        .builder
                        .build_load(i64_type, ptr, &format!("{}_after", name.0))
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let k = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
                    let entry = if k == Kind::Bool {
                        let i1 = self
                            .builder
                            .build_int_truncate(
                                val.into_int_value(),
                                self.context.bool_type(),
                                "after_bool",
                            )
                            .map_err(|e| CompileError::ice(e.to_string()))?;
                        (i1.into(), Kind::Bool)
                    } else {
                        (val, k)
                    };
                    env.insert(name.clone(), entry);
                }
            } else {
                let (out_val, out_ty) = self.compile_expr(output, env)?;
                env.insert(var.clone(), (out_val, out_ty));
                self.compile_stmts(body, env, &alloca_map)?;
            }
        }

        // Propagate final alloca values back into env so subsequent statements see
        // the results of the comprehension loop.
        if filter.is_some() {
            for (name, &ptr) in &alloca_map {
                if name == comp_var {
                    continue;
                }
                if !outer_alloca_map.contains_key(name) {
                    let val = self
                        .builder
                        .build_load(i64_type, ptr, &format!("{}_final", name.0))
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let k = env.get(name).map(|(_, k)| k.clone()).unwrap_or(Kind::Int);
                    let entry = if k == Kind::Bool {
                        let i1 = self
                            .builder
                            .build_int_truncate(
                                val.into_int_value(),
                                self.context.bool_type(),
                                "comp_final_bool",
                            )
                            .map_err(|e| CompileError::ice(e.to_string()))?;
                        (i1.into(), Kind::Bool)
                    } else {
                        (val, k)
                    };
                    env.insert(name.clone(), entry);
                }
            }
        }

        Ok(())
    }
}
