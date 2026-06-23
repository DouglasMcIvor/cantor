use std::collections::HashMap;

use inkwell::values::{AggregateValueEnum, BasicValueEnum, IntValue, PointerValue};

use crate::{
    ast::{AssertElse, Expr, Stmt},
    error::CompileError,
    kind::Kind,
    span::Symbol,
};

use super::{Compiler, Env, FAIL_SENTINEL};

impl<'ctx> Compiler<'ctx> {
    /// Process a sequence of statements, returning the last expression value.
    ///
    /// `alloca_map` is non-empty when compiling a loop body: it maps each
    /// loop-modified variable to its alloca pointer so assignments also write
    /// through to the alloca (making the updated value visible to the loop
    /// header on the next iteration).
    pub(super) fn compile_stmts(
        &mut self,
        stmts: &[Stmt],
        env: &mut Env<'ctx>,
        alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<Option<(BasicValueEnum<'ctx>, Kind)>, CompileError> {
        let mut last = None;
        for stmt in stmts {
            last = None;
            match stmt {
                Stmt::Let { name, value, .. } => {
                    // Immutable: just compile the value and bind the name.
                    // No alloca needed — this name cannot appear in alloca_map
                    // because collect_loop_modified skips Let bindings.
                    let result = self.compile_expr(value, env)?;
                    env.insert(name.clone(), result);
                }

                Stmt::MutLet { name, value, .. } | Stmt::Assign { name, value, .. } => {
                    let result = self.compile_expr(value, env)?;
                    // If this variable is backed by an alloca (i.e. we're in a loop
                    // body and this variable persists across iterations), write
                    // through so the loop header sees the updated value.
                    if let Some(&ptr) = alloca_map.get(name) {
                        let i64_type = self.context.i64_type();
                        let val_i64: IntValue<'ctx> = if result.1 == Kind::Bool {
                            self.builder
                                .build_int_z_extend(result.0.into_int_value(), i64_type, "bool_ext")
                                .map_err(|e| CompileError::Internal(e.to_string()))?
                        } else {
                            result.0.into_int_value()
                        };
                        self.builder
                            .build_store(ptr, val_i64)
                            .map_err(|e| CompileError::Internal(e.to_string()))?;
                    }
                    env.insert(name.clone(), result);
                }

                Stmt::DestructLet { bindings, value, .. } => {
                    let (rhs_val, rhs_kind) = self.compile_expr(value, env)?;
                    let elem_kinds = match rhs_kind {
                        Kind::Tuple(ek) => ek,
                        _ => return Err(CompileError::Internal(
                            "destructuring `=` requires a tuple on the right-hand side".into(),
                        )),
                    };
                    if bindings.len() != elem_kinds.len() {
                        return Err(CompileError::Internal(format!(
                            "destructuring arity mismatch: {} binding(s) but tuple has {} element(s)",
                            bindings.len(), elem_kinds.len()
                        )));
                    }
                    let sv = AggregateValueEnum::StructValue(rhs_val.into_struct_value());
                    for (i, binding) in bindings.iter().enumerate() {
                        let elem = self.builder
                            .build_extract_value(sv, i as u32, &binding.name.0)
                            .map_err(|e| CompileError::Internal(e.to_string()))?;
                        env.insert(binding.name.clone(), (elem, elem_kinds[i].clone()));
                    }
                }

                Stmt::DestructMutLet { bindings, value, .. } => {
                    let (rhs_val, rhs_kind) = self.compile_expr(value, env)?;
                    let elem_kinds = match rhs_kind {
                        Kind::Tuple(ek) => ek,
                        _ => return Err(CompileError::Internal(
                            "destructuring `=` requires a tuple on the right-hand side".into(),
                        )),
                    };
                    if bindings.len() != elem_kinds.len() {
                        return Err(CompileError::Internal(format!(
                            "destructuring arity mismatch: {} binding(s) but tuple has {} element(s)",
                            bindings.len(), elem_kinds.len()
                        )));
                    }
                    let sv = AggregateValueEnum::StructValue(rhs_val.into_struct_value());
                    for (i, binding) in bindings.iter().enumerate() {
                        let elem = self.builder
                            .build_extract_value(sv, i as u32, &binding.name.0)
                            .map_err(|e| CompileError::Internal(e.to_string()))?;
                        if let Some(&ptr) = alloca_map.get(&binding.name) {
                            let i64_type = self.context.i64_type();
                            let val_i64: IntValue<'ctx> = if elem_kinds[i] == Kind::Bool {
                                self.builder
                                    .build_int_z_extend(elem.into_int_value(), i64_type, "bool_ext")
                                    .map_err(|e| CompileError::Internal(e.to_string()))?
                            } else {
                                elem.into_int_value()
                            };
                            self.builder.build_store(ptr, val_i64)
                                .map_err(|e| CompileError::Internal(e.to_string()))?;
                        }
                        env.insert(binding.name.clone(), (elem, elem_kinds[i].clone()));
                    }
                }

                Stmt::DestructAssign { names: dest_names, value, .. } => {
                    let (rhs_val, rhs_kind) = self.compile_expr(value, env)?;
                    let elem_kinds = match rhs_kind {
                        Kind::Tuple(ek) => ek,
                        _ => return Err(CompileError::Internal(
                            "destructuring `:=` requires a tuple on the right-hand side".into(),
                        )),
                    };
                    if dest_names.len() != elem_kinds.len() {
                        return Err(CompileError::Internal(format!(
                            "destructuring arity mismatch: {} name(s) but tuple has {} element(s)",
                            dest_names.len(), elem_kinds.len()
                        )));
                    }
                    let sv = AggregateValueEnum::StructValue(rhs_val.into_struct_value());
                    for (i, name) in dest_names.iter().enumerate() {
                        let elem = self.builder
                            .build_extract_value(sv, i as u32, &name.0)
                            .map_err(|e| CompileError::Internal(e.to_string()))?;
                        if let Some(&ptr) = alloca_map.get(name) {
                            let i64_type = self.context.i64_type();
                            let val_i64: IntValue<'ctx> = if elem_kinds[i] == Kind::Bool {
                                self.builder
                                    .build_int_z_extend(elem.into_int_value(), i64_type, "bool_ext")
                                    .map_err(|e| CompileError::Internal(e.to_string()))?
                            } else {
                                elem.into_int_value()
                            };
                            self.builder.build_store(ptr, val_i64)
                                .map_err(|e| CompileError::Internal(e.to_string()))?;
                        }
                        env.insert(name.clone(), (elem, elem_kinds[i].clone()));
                    }
                }

                // Static-only constructs — no runtime representation.
                Stmt::Require { .. } | Stmt::Assume { .. } => {}

                Stmt::Assert { predicate, else_clause: None, .. } => {
                    self.compile_assert(predicate, env)?;
                }

                Stmt::Assert { predicate, else_clause: Some(else_clause), .. } => {
                    self.compile_assert_else(predicate, else_clause, env)?;
                }

                Stmt::Return { value, .. } => {
                    self.compile_return_stmt(value, env)?;
                }

                Stmt::Expr(e) => {
                    last = Some(self.compile_expr(e, env)?);
                }

                Stmt::Block(inner) => {
                    last = self.compile_stmts(inner, env, alloca_map)?;
                }

                Stmt::While { cond, body, .. } => {
                    self.compile_while(cond, body, env, alloca_map)?;
                }

                Stmt::ForIn { var, set, body, .. } => {
                    self.compile_for_in(var, set, body, env, alloca_map)?;
                }
            }
        }
        Ok(last)
    }

    /// Emit a runtime check for `assert predicate`.
    ///
    /// If the function is fallible, branches to `fail_bb` when the predicate
    /// is false.  In an infallible function, the checker either proved the
    /// assertion or returned Unknown; we skip the check (no runtime overhead).
    pub(super) fn compile_assert(
        &mut self,
        predicate: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let Some(fail_bb) = self.fail_bb else {
            return Err(CompileError::Internal(
                "assert in a function whose return type does not include `Fail` \
                 was not eliminated by the solver — add `| Fail` to the return type \
                 or prove the assertion statically"
                    .into(),
            ));
        };

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::Internal("assert outside a function".into()))?;

        let (cond_val, _) = self.compile_expr(predicate, env)?;
        let cond_i1 = cond_val.into_int_value();

        let pass_bb = self.context.append_basic_block(function, "assert_pass");
        self.builder
            .build_conditional_branch(cond_i1, pass_bb, fail_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        self.builder.position_at_end(pass_bb);
        Ok(())
    }

    /// Emit a runtime check for `assert predicate else <clause>`.
    ///
    /// When the predicate is false: for `else fail expr`, compute the offset-encoded
    /// failure value and return it; for `else return expr`, evaluate the expression
    /// and return it directly.  Both cases position the builder on a dead block after
    /// the early return so inkwell doesn't require a terminator.
    pub(super) fn compile_assert_else(
        &mut self,
        predicate: &Expr,
        else_clause: &AssertElse,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::Internal("assert outside a function".into()))?;

        let (cond_val, _) = self.compile_expr(predicate, env)?;
        let cond_i1 = cond_val.into_int_value();

        let fail_out_bb = self.context.append_basic_block(function, "assert_else_fail");
        let pass_bb     = self.context.append_basic_block(function, "assert_else_pass");

        self.builder
            .build_conditional_branch(cond_i1, pass_bb, fail_out_bb)
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // ── else branch: emit the value to return and exit early ──────────────
        self.builder.position_at_end(fail_out_bb);
        let else_val: BasicValueEnum<'ctx> = match else_clause {
            AssertElse::FailWith(fail_expr) => {
                let (v, _) = self.compile_expr(fail_expr, env)?;
                let n = v.into_int_value();
                let i64t = self.context.i64_type();
                let base = i64t.const_int(FAIL_SENTINEL.wrapping_add(1) as u64, true);
                self.builder
                    .build_int_add(base, n, "fail_encoded")
                    .map_err(|e| CompileError::Internal(e.to_string()))?
                    .into()
            }
            AssertElse::Return(ret_expr) => {
                let (v, kind) = self.compile_expr(ret_expr, env)?;
                if kind == Kind::Bool {
                    let i64t = self.context.i64_type();
                    self.builder
                        .build_int_z_extend(v.into_int_value(), i64t, "ret_bool_ext")
                        .map_err(|e| CompileError::Internal(e.to_string()))?
                        .into()
                } else {
                    v
                }
            }
        };
        self.builder
            .build_return(Some(&else_val))
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // Position on a dead block so inkwell doesn't need a terminator after the return.
        let dead = self.context.append_basic_block(function, "assert_else_dead");
        self.builder.position_at_end(dead);

        // ── pass branch: normal continuation ──────────────────────────────────
        self.builder.position_at_end(pass_bb);
        Ok(())
    }

    /// Emit an early `return value` from the current function.
    ///
    /// Positions the builder on a dead basic block after emitting the return
    /// instruction, so subsequent statements (unreachable by definition) don't
    /// need a terminator.
    pub(super) fn compile_return_stmt(
        &mut self,
        value: &Expr,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::Internal("`return` outside a function".into()))?;

        let (v, kind) = self.compile_expr(value, env)?;
        let i64t = self.context.i64_type();
        let ret_val: BasicValueEnum<'ctx> = if kind == Kind::Bool {
            self.builder
                .build_int_z_extend(v.into_int_value(), i64t, "ret_bool_ext")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into()
        } else {
            v
        };
        self.builder
            .build_return(Some(&ret_val))
            .map_err(|e| CompileError::Internal(e.to_string()))?;

        // Dead block to satisfy inkwell's requirement for a current insert point.
        let dead = self.context.append_basic_block(function, "after_return");
        self.builder.position_at_end(dead);

        Ok(())
    }
}
