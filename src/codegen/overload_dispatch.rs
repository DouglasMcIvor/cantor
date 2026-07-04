//! Runtime membership-test dispatch chain for overloaded calls the solver
//! couldn't statically resolve (int-soundness-plan phase 2).
//!
//! Split out of `expr.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — mirrors phase 1's own
//! `encode.rs` → `encode_call.rs` split.

use inkwell::values::{BasicValue, BasicValueEnum, IntValue};

use crate::{
    error::CompileError,
    semantics::tree::SemExpr,
    span::{Span, Symbol},
};

use super::{Compiler, OverloadEntry};

/// Which LLVM function(s) a call to an (possibly-)overloaded name compiles
/// to — see `Compiler::resolve_overload_call_target`.
pub(super) enum CallTarget<'a> {
    Direct(String),
    Dispatch(Vec<&'a OverloadEntry>),
}

impl<'ctx> Compiler<'ctx> {
    /// Decide which LLVM function(s) a call to `callee` compiles to, and the
    /// "lookup key" whose `fn_param_kinds`/`fn_param_set_exprs`/`fn_return_kinds`
    /// entry describes the ABI shared by every arity-matching candidate.
    ///
    /// Absent from `overload_dispatch` ⇒ today's plain path, unchanged (the
    /// overwhelming common case). Present ⇒ resolve which candidate(s) this
    /// call's arity admits, then either a direct call (arity alone, or a
    /// solver-proved resolution, picked exactly one) or a runtime
    /// membership-test dispatch chain.
    pub(super) fn resolve_overload_call_target(
        &self,
        callee: &Symbol,
        args: &[SemExpr],
        span: Span,
    ) -> Result<(String, CallTarget<'_>), CompileError> {
        match self.overload_dispatch.get(&callee.0) {
            None => Ok((callee.0.clone(), CallTarget::Direct(callee.0.clone()))),
            Some(entries) => {
                let matching: Vec<&OverloadEntry> =
                    entries.iter().filter(|e| e.arity == args.len()).collect();
                if matching.is_empty() {
                    return Err(CompileError::ice(format!(
                        "no overload of `{}` accepts {} argument(s) — the solver should have \
                         rejected this call before codegen ever saw it",
                        callee.0,
                        args.len()
                    )));
                }
                if let [only] = matching.as_slice() {
                    Ok((
                        only.mangled_name.clone(),
                        CallTarget::Direct(only.mangled_name.clone()),
                    ))
                } else if let Some(&idx) = self.overload_resolution.get(&span) {
                    let resolved = entries
                        .get(idx)
                        .filter(|e| e.arity == args.len())
                        .ok_or_else(|| {
                            CompileError::ice(
                                "overload_resolution index out of range or arity mismatch",
                            )
                        })?;
                    Ok((
                        resolved.mangled_name.clone(),
                        CallTarget::Direct(resolved.mangled_name.clone()),
                    ))
                } else {
                    // Every arity-matching candidate agrees on Kind
                    // (elaboration enforced this), so any one of them
                    // describes the param_kinds/param_set_exprs shared by
                    // all of them, used for arg coercion at the call site —
                    // `matching[0]` is as good as any (see `OverloadEntry`'s
                    // doc comment for the one place this representative
                    // choice is imprecise: a candidate with more than one
                    // signature of its own).
                    Ok((
                        matching[0].mangled_name.clone(),
                        CallTarget::Dispatch(matching),
                    ))
                }
            }
        }
    }

    /// int-soundness-plan phase 2: runtime membership-test dispatch chain for
    /// an overloaded call the solver couldn't statically resolve.
    ///
    /// `candidates` (arity-matching, file order) each get a domain
    /// membership test in turn — order is irrelevant since domains are
    /// solver-proved disjoint. The final else-arm is unreachable *by proof*,
    /// not by construction: it still emits a loud runtime trap
    /// (`cantor_dispatch_unreachable`) rather than silently falling through,
    /// per CLAUDE.md's fail-loudly principle — a defense against a
    /// solver/codegen disagreement, not an expected runtime path.
    pub(super) fn compile_overload_dispatch(
        &self,
        callee_name: &str,
        candidates: &[&OverloadEntry],
        arg_values: &[BasicValueEnum<'ctx>],
        compiled_args: &[inkwell::values::BasicMetadataValueEnum<'ctx>],
        span: Span,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("overloaded call outside a function"))?;
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());

        let merge_bb = self.context.append_basic_block(function, "ov_merge");
        let trap_bb = self.context.append_basic_block(function, "ov_trap");

        let mut incoming: Vec<(BasicValueEnum<'ctx>, inkwell::basic_block::BasicBlock<'ctx>)> =
            Vec::new();
        let mut check_bb = self
            .builder
            .get_insert_block()
            .ok_or_else(|| CompileError::ice("no current basic block"))?;

        for entry in candidates {
            self.builder.position_at_end(check_bb);
            let matches = self.compile_overload_domain_match(entry, arg_values)?;

            let call_bb = self.context.append_basic_block(function, "ov_call");
            let next_check_bb = self.context.append_basic_block(function, "ov_check");
            self.builder
                .build_conditional_branch(matches, call_bb, next_check_bb)
                .map_err(err)?;

            self.builder.position_at_end(call_bb);
            let fn_val = self
                .module
                .get_function(&entry.mangled_name)
                .ok_or_else(|| CompileError::ice(format!("{} not declared", entry.mangled_name)))?;
            let call = self
                .builder
                .build_call(fn_val, compiled_args, "ov_call")
                .map_err(err)?;
            let result = call
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice("void return in expression position"))?;
            let call_bb_end = self.builder.get_insert_block().unwrap();
            self.builder
                .build_unconditional_branch(merge_bb)
                .map_err(err)?;
            incoming.push((result, call_bb_end));

            check_bb = next_check_bb;
        }

        // `check_bb` is now the final "no candidate matched" block.
        self.builder.position_at_end(check_bb);
        self.builder
            .build_unconditional_branch(trap_bb)
            .map_err(err)?;

        self.builder.position_at_end(trap_bb);
        let message = self.overload_dispatch_trap_message(callee_name, span);
        let msg_global = self
            .builder
            .build_global_string_ptr(&message, "ov_trap_msg")
            .map_err(err)?;
        let msg_i64 = self
            .builder
            .build_ptr_to_int(
                msg_global.as_pointer_value(),
                self.context.i64_type(),
                "ov_trap_msg_i64",
            )
            .map_err(err)?;
        let trap_fn = self
            .module
            .get_function("cantor_dispatch_unreachable")
            .ok_or_else(|| CompileError::ice("cantor_dispatch_unreachable not declared"))?;
        self.builder
            .build_call(trap_fn, &[msg_i64.into()], "ov_trap_call")
            .map_err(err)?;
        self.builder.build_unreachable().map_err(err)?;

        self.builder.position_at_end(merge_bb);
        let phi = self
            .builder
            .build_phi(incoming[0].0.get_type(), "ov_result")
            .map_err(err)?;
        let incoming_refs: Vec<(
            &dyn BasicValue<'ctx>,
            inkwell::basic_block::BasicBlock<'ctx>,
        )> = incoming
            .iter()
            .map(|(v, bb)| (v as &dyn BasicValue<'ctx>, *bb))
            .collect();
        phi.add_incoming(&incoming_refs);
        Ok(phi.as_basic_value())
    }

    /// AND across parameter positions of `compile_membership(arg_i, domain_i)`
    /// for one overload candidate — an empty `domain_parts` (candidate whose
    /// domain didn't decompose at declare time) is trivially always-true.
    fn compile_overload_domain_match(
        &self,
        entry: &OverloadEntry,
        arg_values: &[BasicValueEnum<'ctx>],
    ) -> Result<IntValue<'ctx>, CompileError> {
        if entry.domain_parts.is_empty() {
            return Ok(self.context.bool_type().const_int(1, false));
        }
        let mut acc: Option<IntValue<'ctx>> = None;
        for (val, part) in arg_values.iter().zip(&entry.domain_parts) {
            let m = self.compile_membership(val.into_int_value(), part)?;
            acc = Some(match acc {
                None => m,
                Some(a) => self
                    .builder
                    .build_and(a, m, "ov_domain_and")
                    .map_err(|e| CompileError::ice(e.to_string()))?,
            });
        }
        Ok(acc.unwrap_or_else(|| self.context.bool_type().const_int(1, false)))
    }

    /// Format an overload-dispatch trap message, `path:line:col`-prefixed
    /// when `overflow_ctx` is available (same source of path/src as
    /// `overflow_message` — both are populated together from the same
    /// verified `ConstrainedTree`), falling back to a bare message otherwise.
    fn overload_dispatch_trap_message(&self, callee_name: &str, span: Span) -> String {
        let msg = format!(
            "no overload of `{callee_name}` matched at runtime (internal error — the solver \
             should have proved union coverage)"
        );
        match &self.overflow_ctx {
            Some((path, src)) => {
                let (line, col) = crate::span::offset_to_line_col(src, span.start);
                format!("{path}:{line}:{col}: {msg}")
            }
            None => msg,
        }
    }
}
