use std::collections::HashMap;

use inkwell::values::{AggregateValueEnum, BasicValueEnum, IntValue, PointerValue};

use crate::{
    error::CompileError,
    kind::Kind,
    semantics::tree::{SemAssertElse, SemExpr, SemStmt},
    span::Symbol,
};

use super::{Compiler, Env};

impl<'ctx> Compiler<'ctx> {
    /// Process a sequence of statements, returning the last expression value.
    ///
    /// `alloca_map` is non-empty when compiling a loop body: it maps each
    /// loop-modified variable to its alloca pointer so assignments also write
    /// through to the alloca (making the updated value visible to the loop
    /// header on the next iteration).
    pub(super) fn compile_stmts(
        &mut self,
        stmts: &[SemStmt],
        env: &mut Env<'ctx>,
        alloca_map: &HashMap<Symbol, PointerValue<'ctx>>,
    ) -> Result<Option<(BasicValueEnum<'ctx>, Kind)>, CompileError> {
        let mut last = None;
        for stmt in stmts {
            last = None;
            match stmt {
                SemStmt::Let {
                    name,
                    constraint,
                    value,
                    ..
                } => {
                    // Immutable: compile the value, optionally coerce to a vector, and bind.
                    // No alloca needed — this name cannot appear in alloca_map
                    // because collect_loop_modified skips Let bindings.
                    let result = self.compile_expr(value, env)?;
                    let result = coerce_to_vector_if_needed(self, result, constraint)?;
                    env.insert(name.clone(), result);
                }

                SemStmt::MutLet {
                    name,
                    constraint,
                    value,
                    ..
                } => {
                    let result = self.compile_expr(value, env)?;
                    let result = coerce_to_vector_if_needed(self, result, constraint)?;
                    // If this variable is backed by an alloca (i.e. we're in a loop
                    // body and this variable persists across iterations), write
                    // through so the loop header sees the updated value.
                    if let Some(&ptr) = alloca_map.get(name) {
                        let i64_type = self.context.i64_type();
                        let val_i64: IntValue<'ctx> = if result.1 == Kind::Bool {
                            self.builder
                                .build_int_z_extend(result.0.into_int_value(), i64_type, "bool_ext")
                                .map_err(|e| CompileError::ice(e.to_string()))?
                        } else {
                            result.0.into_int_value()
                        };
                        self.builder
                            .build_store(ptr, val_i64)
                            .map_err(|e| CompileError::ice(e.to_string()))?;
                    }
                    env.insert(name.clone(), result);
                }

                SemStmt::Assign { name, value, .. } => {
                    let result = self.compile_expr(value, env)?;
                    // If this variable is backed by an alloca (i.e. we're in a loop
                    // body and this variable persists across iterations), write
                    // through so the loop header sees the updated value.
                    if let Some(&ptr) = alloca_map.get(name) {
                        let i64_type = self.context.i64_type();
                        let val_i64: IntValue<'ctx> = if result.1 == Kind::Bool {
                            self.builder
                                .build_int_z_extend(result.0.into_int_value(), i64_type, "bool_ext")
                                .map_err(|e| CompileError::ice(e.to_string()))?
                        } else {
                            result.0.into_int_value()
                        };
                        self.builder
                            .build_store(ptr, val_i64)
                            .map_err(|e| CompileError::ice(e.to_string()))?;
                    }
                    env.insert(name.clone(), result);
                }

                SemStmt::DestructLet {
                    bindings, value, ..
                } => {
                    let (rhs_val, rhs_kind) = self.compile_expr(value, env)?;
                    let elem_kinds = match rhs_kind {
                        Kind::Tuple(ek) => ek,
                        // See the matching guard in `elaborate_destruct_bindings` —
                        // elaboration should already reject this before codegen
                        // ever sees it; kept here as defense in depth.
                        Kind::Vector(_) => {
                            return Err(CompileError::ice(
                                "not yet implemented: destructuring a vector (`X*`) — \
                             only tuple right-hand sides are currently supported",
                            ));
                        }
                        _ => {
                            return Err(CompileError::ice(
                                "destructuring `=` requires a tuple on the right-hand side",
                            ));
                        }
                    };
                    if bindings.len() > elem_kinds.len() {
                        return Err(CompileError::ice(format!(
                            "destructuring arity mismatch: {} binding(s) but tuple has only {} element(s)",
                            bindings.len(),
                            elem_kinds.len()
                        )));
                    }
                    let sv = AggregateValueEnum::StructValue(rhs_val.into_struct_value());
                    let last_i = bindings.len() - 1;
                    for (i, binding) in bindings.iter().enumerate() {
                        let tail_count = elem_kinds.len() - i;
                        let (elem, kind) = if i < last_i || tail_count == 1 {
                            let e = self
                                .builder
                                .build_extract_value(sv, i as u32, &binding.name.0)
                                .map_err(|e| CompileError::ice(e.to_string()))?;
                            (e, elem_kinds[i].clone())
                        } else {
                            // Last binder receives the remaining elements as a sub-tuple.
                            let tail_kinds: Vec<Kind> = elem_kinds[i..].to_vec();
                            let llvm_types: Vec<_> = tail_kinds
                                .iter()
                                .map(|k| self.kind_to_llvm_type(k))
                                .collect();
                            let struct_ty = self.context.struct_type(&llvm_types, false);
                            let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
                            for (j, _) in tail_kinds.iter().enumerate() {
                                let e = self
                                    .builder
                                    .build_extract_value(
                                        sv,
                                        (i + j) as u32,
                                        &format!("{}_t{}", binding.name.0, j),
                                    )
                                    .map_err(|e| CompileError::ice(e.to_string()))?;
                                agg = self
                                    .builder
                                    .build_insert_value(agg, e, j as u32, "ts")
                                    .map_err(|e| CompileError::ice(e.to_string()))?;
                            }
                            (agg.into_struct_value().into(), Kind::Tuple(tail_kinds))
                        };
                        env.insert(binding.name.clone(), (elem, kind));
                    }
                }

                SemStmt::DestructMutLet {
                    bindings, value, ..
                } => {
                    let (rhs_val, rhs_kind) = self.compile_expr(value, env)?;
                    let elem_kinds = match rhs_kind {
                        Kind::Tuple(ek) => ek,
                        // See the matching guard in `elaborate_destruct_bindings` —
                        // elaboration should already reject this before codegen
                        // ever sees it; kept here as defense in depth.
                        Kind::Vector(_) => {
                            return Err(CompileError::ice(
                                "not yet implemented: destructuring a vector (`X*`) — \
                             only tuple right-hand sides are currently supported",
                            ));
                        }
                        _ => {
                            return Err(CompileError::ice(
                                "destructuring `=` requires a tuple on the right-hand side",
                            ));
                        }
                    };
                    if bindings.len() > elem_kinds.len() {
                        return Err(CompileError::ice(format!(
                            "destructuring arity mismatch: {} binding(s) but tuple has only {} element(s)",
                            bindings.len(),
                            elem_kinds.len()
                        )));
                    }
                    let sv = AggregateValueEnum::StructValue(rhs_val.into_struct_value());
                    let last_i = bindings.len() - 1;
                    for (i, binding) in bindings.iter().enumerate() {
                        let tail_count = elem_kinds.len() - i;
                        let (elem, kind) = if i < last_i || tail_count == 1 {
                            let e = self
                                .builder
                                .build_extract_value(sv, i as u32, &binding.name.0)
                                .map_err(|e| CompileError::ice(e.to_string()))?;
                            (e, elem_kinds[i].clone())
                        } else {
                            // Last binder receives the remaining elements as a sub-tuple.
                            // TODO: loop alloca write-through for tuple tail binders is not yet
                            // implemented; panic if the tail binding is loop-modified.
                            if alloca_map.contains_key(&binding.name) {
                                panic!(
                                    "TODO: mutable tuple tail binder `{}` modified inside a loop \
                                     is not yet supported",
                                    binding.name.0
                                );
                            }
                            let tail_kinds: Vec<Kind> = elem_kinds[i..].to_vec();
                            let llvm_types: Vec<_> = tail_kinds
                                .iter()
                                .map(|k| self.kind_to_llvm_type(k))
                                .collect();
                            let struct_ty = self.context.struct_type(&llvm_types, false);
                            let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
                            for (j, _) in tail_kinds.iter().enumerate() {
                                let e = self
                                    .builder
                                    .build_extract_value(
                                        sv,
                                        (i + j) as u32,
                                        &format!("{}_t{}", binding.name.0, j),
                                    )
                                    .map_err(|e| CompileError::ice(e.to_string()))?;
                                agg = self
                                    .builder
                                    .build_insert_value(agg, e, j as u32, "ts")
                                    .map_err(|e| CompileError::ice(e.to_string()))?;
                            }
                            (agg.into_struct_value().into(), Kind::Tuple(tail_kinds))
                        };
                        if let Some(&ptr) = alloca_map.get(&binding.name) {
                            let i64_type = self.context.i64_type();
                            let val_i64: IntValue<'ctx> = if kind == Kind::Bool {
                                self.builder
                                    .build_int_z_extend(elem.into_int_value(), i64_type, "bool_ext")
                                    .map_err(|e| CompileError::ice(e.to_string()))?
                            } else {
                                elem.into_int_value()
                            };
                            self.builder
                                .build_store(ptr, val_i64)
                                .map_err(|e| CompileError::ice(e.to_string()))?;
                        }
                        env.insert(binding.name.clone(), (elem, kind));
                    }
                }

                SemStmt::DestructAssign {
                    names: dest_names,
                    value,
                    ..
                } => {
                    let (rhs_val, rhs_kind) = self.compile_expr(value, env)?;
                    let elem_kinds = match rhs_kind {
                        Kind::Tuple(ek) => ek,
                        // See the matching guard in `elaborate_destruct_bindings` —
                        // elaboration should already reject this before codegen
                        // ever sees it; kept here as defense in depth.
                        Kind::Vector(_) => {
                            return Err(CompileError::ice(
                                "not yet implemented: destructuring a vector (`X*`) — \
                             only tuple right-hand sides are currently supported",
                            ));
                        }
                        _ => {
                            return Err(CompileError::ice(
                                "destructuring `:=` requires a tuple on the right-hand side",
                            ));
                        }
                    };
                    if dest_names.len() > elem_kinds.len() {
                        return Err(CompileError::ice(format!(
                            "destructuring arity mismatch: {} name(s) but tuple has only {} element(s)",
                            dest_names.len(),
                            elem_kinds.len()
                        )));
                    }
                    let sv = AggregateValueEnum::StructValue(rhs_val.into_struct_value());
                    let last_i = dest_names.len() - 1;
                    for (i, name) in dest_names.iter().enumerate() {
                        let tail_count = elem_kinds.len() - i;
                        let (elem, kind) = if i < last_i || tail_count == 1 {
                            let e = self
                                .builder
                                .build_extract_value(sv, i as u32, &name.0)
                                .map_err(|e| CompileError::ice(e.to_string()))?;
                            (e, elem_kinds[i].clone())
                        } else {
                            // TODO: loop alloca write-through for tuple tail binders not yet supported.
                            if alloca_map.contains_key(name) {
                                panic!(
                                    "TODO: tuple tail binder `{}` modified inside a loop \
                                     is not yet supported",
                                    name.0
                                );
                            }
                            let tail_kinds: Vec<Kind> = elem_kinds[i..].to_vec();
                            let llvm_types: Vec<_> = tail_kinds
                                .iter()
                                .map(|k| self.kind_to_llvm_type(k))
                                .collect();
                            let struct_ty = self.context.struct_type(&llvm_types, false);
                            let mut agg: AggregateValueEnum<'ctx> = struct_ty.get_undef().into();
                            for (j, _) in tail_kinds.iter().enumerate() {
                                let e = self
                                    .builder
                                    .build_extract_value(
                                        sv,
                                        (i + j) as u32,
                                        &format!("{}_t{}", name.0, j),
                                    )
                                    .map_err(|e| CompileError::ice(e.to_string()))?;
                                agg = self
                                    .builder
                                    .build_insert_value(agg, e, j as u32, "ts")
                                    .map_err(|e| CompileError::ice(e.to_string()))?;
                            }
                            (agg.into_struct_value().into(), Kind::Tuple(tail_kinds))
                        };
                        if let Some(&ptr) = alloca_map.get(name) {
                            let i64_type = self.context.i64_type();
                            let val_i64: IntValue<'ctx> = if kind == Kind::Bool {
                                self.builder
                                    .build_int_z_extend(elem.into_int_value(), i64_type, "bool_ext")
                                    .map_err(|e| CompileError::ice(e.to_string()))?
                            } else {
                                elem.into_int_value()
                            };
                            self.builder
                                .build_store(ptr, val_i64)
                                .map_err(|e| CompileError::ice(e.to_string()))?;
                        }
                        env.insert(name.clone(), (elem, kind));
                    }
                }

                // Static-only constructs — no runtime representation.
                SemStmt::Require { .. } | SemStmt::Assume { .. } => {}

                SemStmt::Assert {
                    predicate,
                    else_clause: None,
                    ..
                } => {
                    self.compile_assert(predicate, env)?;
                }

                SemStmt::Assert {
                    predicate,
                    else_clause: Some(else_clause),
                    ..
                } => {
                    self.compile_assert_else(predicate, else_clause, env)?;
                }

                SemStmt::Return { value, .. } => {
                    self.compile_return_stmt(value, env)?;
                }

                SemStmt::Expr(e) => {
                    last = Some(self.compile_expr(e, env)?);
                }

                SemStmt::Block(inner) => {
                    last = self.compile_stmts(inner, env, alloca_map)?;
                }

                SemStmt::While { cond, body, .. } => {
                    self.compile_while(cond, body, env, alloca_map)?;
                }

                SemStmt::ForIn { var, set, body, .. } => {
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
        predicate: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let Some(fail_bb) = self.fail_bb else {
            return Err(CompileError::ice(
                "assert in a function whose return type does not include `Fail` \
                 was not eliminated by the solver — add `| Fail` to the return type \
                 or prove the assertion statically",
            ));
        };

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("assert outside a function"))?;

        let (cond_val, _) = self.compile_expr(predicate, env)?;
        let cond_i1 = cond_val.into_int_value();

        let pass_bb = self.context.append_basic_block(function, "assert_pass");
        self.builder
            .build_conditional_branch(cond_i1, pass_bb, fail_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

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
        predicate: &SemExpr,
        else_clause: &SemAssertElse,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("assert outside a function"))?;

        let (cond_val, _) = self.compile_expr(predicate, env)?;
        let cond_i1 = cond_val.into_int_value();

        let fail_out_bb = self
            .context
            .append_basic_block(function, "assert_else_fail");
        let pass_bb = self
            .context
            .append_basic_block(function, "assert_else_pass");

        self.builder
            .build_conditional_branch(cond_i1, pass_bb, fail_out_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // ── else branch: emit the value to return and exit early ──────────────
        self.builder.position_at_end(fail_out_bb);
        let else_val: BasicValueEnum<'ctx> = match else_clause {
            SemAssertElse::FailWith(fail_expr) => {
                // `assert pred else fail n` → return {i1=1, i64=n}
                let (v, _) = self.compile_expr(fail_expr, env)?;
                self.build_fail_struct(v)?
            }
            SemAssertElse::Return(ret_expr) => {
                // `assert pred else return expr` → return normally (may be success or fail struct)
                let (v, kind) = self.compile_expr(ret_expr, env)?;
                self.wrap_return_value(v, &kind)?
            }
        };
        self.builder
            .build_return(Some(&else_val))
            .map_err(|e| CompileError::ice(e.to_string()))?;

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
        value: &SemExpr,
        env: &Env<'ctx>,
    ) -> Result<(), CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("`return` outside a function"))?;

        let (v, kind) = self.compile_expr(value, env)?;
        let (v, kind) = self.coerce_int_return(v, kind, function)?;
        let ret_val = self.wrap_return_value(v, &kind)?;
        self.builder
            .build_return(Some(&ret_val))
            .map_err(|e| CompileError::ice(e.to_string()))?;

        // Dead block to satisfy inkwell's requirement for a current insert point.
        let dead = self.context.append_basic_block(function, "after_return");
        self.builder.position_at_end(dead);

        Ok(())
    }
}

/// If the constraint expression is a Kleene-star set (`X*`) and the compiled
/// value is a tuple (array literal), coerce the tuple to a vector.
/// Otherwise return the value unchanged.
fn coerce_to_vector_if_needed<'ctx>(
    compiler: &Compiler<'ctx>,
    (val, kind): (inkwell::values::BasicValueEnum<'ctx>, Kind),
    constraint: &SemExpr,
) -> Result<(inkwell::values::BasicValueEnum<'ctx>, Kind), CompileError> {
    let elem_kind = match &constraint.kind_of {
        Kind::Vector(ek) => ek.as_ref().clone(),
        _ => return Ok((val, kind)),
    };
    match &kind {
        Kind::Tuple(elems) => {
            let elems = elems.clone();
            compiler.compile_tuple_as_vector(val, &elems, &elem_kind)
        }
        Kind::Vector(_) => Ok((val, kind)), // already a vector, no coercion needed
        _ => Ok((val, kind)),               // not a coercible kind; solver will catch mismatches
    }
}
