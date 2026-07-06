//! Checked/tagged arithmetic: `+ - * /` and unary `-`.
//!
//! Split out of `expr.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline — mirrors phase 1's own
//! `encode.rs` → `encode_call.rs` split and phase 2's `expr.rs` →
//! `overload_dispatch.rs` split.

use inkwell::{
    IntPredicate,
    intrinsics::Intrinsic,
    values::{AggregateValueEnum, BasicValueEnum, IntValue},
};

use crate::{
    ast::{BinOp, UnOp},
    error::CompileError,
    kind::Kind,
    semantics::tree::SemExpr,
    span::Span,
};

use super::{Compiler, Env};

impl<'ctx> Compiler<'ctx> {
    /// Value-position `+ - * /` — dedicated `SemExprKind` variants (never
    /// wrapped in `BinOp`, see `tree.rs`'s module doc).
    ///
    /// int-soundness-plan phase 1: when the solver proved this node's result
    /// fits in `Int64` (`self.overflow_checks`), emits today's plain
    /// instruction — zero cost. Otherwise emits a checked instruction that
    /// aborts at runtime rather than silently wrapping; unproved is the
    /// common case (`Mul` under an unconstrained domain is nonlinear
    /// arithmetic the solver can't decide), and is deliberately *not* a
    /// compile error — see docs/int-soundness-plan.md.
    pub(super) fn compile_arith(
        &self,
        op: BinOp,
        lhs: &SemExpr,
        rhs: &SemExpr,
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (lv, lk) = self.compile_expr(lhs, env)?;
        let (rv, rk) = self.compile_expr(rhs, env)?;
        let li = self.scalarize_to_int(lv, &lk)?;
        let ri = self.scalarize_to_int(rv, &rk)?;

        // Signed32/Unsigned32 (docs/wrapping-and-quotient-sets-plan.md):
        // plain i32 `add`/`sub`/`mul` with no `nsw`/`nuw` flags is already
        // exactly two's-complement wraparound — nothing to prove, nothing
        // to tag, nothing that can overflow. `/` on a wrapping sort is a
        // clean compile-time error at the solver layer (division isn't a
        // ring homomorphism mod 2^32, deliberately deferred), so a
        // same-family Div should never actually reach codegen — this ICE is
        // a defensive "the solver should have already rejected this", not a
        // live path.
        if matches!(lk, Kind::Signed32 | Kind::Unsigned32) {
            let v = match op {
                BinOp::Add => self.builder.build_int_add(li, ri, "wadd"),
                BinOp::Sub => self.builder.build_int_sub(li, ri, "wsub"),
                BinOp::Mul => self.builder.build_int_mul(li, ri, "wmul"),
                _ => {
                    return Err(CompileError::ice(format!(
                        "`{op}` on a wrapping fixed-width integer reached codegen — the \
                         solver should have already rejected this at compile time"
                    )));
                }
            }
            .map_err(|e| CompileError::ice(e.to_string()))?;
            return Ok((v.into(), lk));
        }

        // int-soundness-plan phase 3 step 4b: only a node whose *actual*
        // operand values are both raw `Int64` stays on the fast/checked raw
        // path below — anything touching a tagged `Kind::Int` operand (the
        // common case for a genuinely-unbounded position, or a mix, e.g. a
        // Step-A-promoted call's raw result combined with an ordinary tagged
        // local) routes through the tagged `cantor_bigint_*` runtime
        // functions instead, which never overflow (they promote to a boxed
        // `BigInt` internally). `ensure_tagged` is a no-op for an operand
        // that's already tagged.
        if self.tagging_active() && !(lk == Kind::Int64 && rk == Kind::Int64) {
            let li = self.ensure_tagged(li, &lk)?;
            let ri = self.ensure_tagged(ri, &rk)?;
            let fn_name = match op {
                BinOp::Add => "cantor_bigint_add",
                BinOp::Sub => "cantor_bigint_sub",
                BinOp::Mul => "cantor_bigint_mul",
                BinOp::Div => "cantor_bigint_div",
                _ => unreachable!("compile_arith is only called for Add/Sub/Mul/Div"),
            };
            let fn_val = self
                .module
                .get_function(fn_name)
                .ok_or_else(|| CompileError::ice(format!("{fn_name} not declared")))?;
            let result = self
                .builder
                .build_call(fn_val, &[li.into(), ri.into()], "bigint_arith")
                .map_err(|e| CompileError::ice(e.to_string()))?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice(format!("{fn_name} returned void")))?;
            return Ok((result, Kind::Int));
        }

        let proved = self.overflow_checks.get(&span).copied().unwrap_or(false);
        let b = &self.builder;
        // Outside the verified pipeline (see `tagging_active`'s doc comment)
        // `Kind::Int64` never appears anywhere else, so this path must still
        // report the historic `Kind::Int` — only once tagging is genuinely
        // active does reaching this raw path mean both operands were really
        // `Int64`.
        let raw_result_kind = if self.tagging_active() {
            Kind::Int64
        } else {
            Kind::Int
        };

        if proved {
            let v = match op {
                BinOp::Add => b.build_int_add(li, ri, "add"),
                BinOp::Sub => b.build_int_sub(li, ri, "sub"),
                BinOp::Mul => b.build_int_mul(li, ri, "mul"),
                BinOp::Div => b.build_int_signed_div(li, ri, "div"),
                _ => unreachable!("compile_arith is only called for Add/Sub/Mul/Div"),
            }
            .map_err(|e| CompileError::ice(e.to_string()))?;
            return Ok((v.into(), raw_result_kind));
        }

        let v = match op {
            BinOp::Add => self.emit_checked_arith_i64("llvm.sadd.with.overflow", li, ri, span)?,
            BinOp::Sub => self.emit_checked_arith_i64("llvm.ssub.with.overflow", li, ri, span)?,
            BinOp::Mul => self.emit_checked_arith_i64("llvm.smul.with.overflow", li, ri, span)?,
            // Divisor-nonzero is already a hard proof gate (untouched by this
            // phase); the only remaining overflow case is `i64::MIN / -1`
            // (UB in LLVM's `sdiv`), which has no `with.overflow` intrinsic —
            // an explicit guard is cheaper anyway since both operands are
            // already valid i64 words by this point.
            BinOp::Div => {
                let i64_type = self.context.i64_type();
                let min = i64_type.const_int(i64::MIN as u64, true);
                let neg_one = i64_type.const_all_ones();
                let is_min = b
                    .build_int_compare(IntPredicate::EQ, li, min, "div_lhs_is_min")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let is_neg_one = b
                    .build_int_compare(IntPredicate::EQ, ri, neg_one, "div_rhs_is_neg_one")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let overflow = b
                    .build_and(is_min, is_neg_one, "div_overflow")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                self.emit_overflow_abort_branch(overflow, span)?;
                b.build_int_signed_div(li, ri, "div")
                    .map_err(|e| CompileError::ice(e.to_string()))?
            }
            _ => unreachable!("compile_arith is only called for Add/Sub/Mul/Div"),
        };
        Ok((v.into(), raw_result_kind))
    }

    /// Emit an LLVM `llvm.{s}.with.overflow.i64` intrinsic call for `l op r`,
    /// then an overflow-abort branch (`emit_overflow_abort_branch`) gated on
    /// the intrinsic's overflow flag. Returns the (possibly-wrapped, but only
    /// reached when the flag is false) result.
    fn emit_checked_arith_i64(
        &self,
        intrinsic_name: &str,
        l: IntValue<'ctx>,
        r: IntValue<'ctx>,
        span: Span,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let i64_type = self.context.i64_type();
        let intrinsic = Intrinsic::find(intrinsic_name).ok_or_else(|| {
            CompileError::ice(format!("LLVM intrinsic `{intrinsic_name}` not found"))
        })?;
        let decl = intrinsic
            .get_declaration(&self.module, &[i64_type.into()])
            .ok_or_else(|| {
                CompileError::ice(format!(
                    "could not declare LLVM intrinsic `{intrinsic_name}`"
                ))
            })?;
        let call = self
            .builder
            .build_call(decl, &[l.into(), r.into()], "checked_arith")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let agg = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| {
                CompileError::ice(format!("`{intrinsic_name}` returned void unexpectedly"))
            })?
            .into_struct_value();

        let result = self
            .builder
            .build_extract_value(AggregateValueEnum::StructValue(agg), 0, "checked_result")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();
        let overflow = self
            .builder
            .build_extract_value(AggregateValueEnum::StructValue(agg), 1, "checked_overflow")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();

        self.emit_overflow_abort_branch(overflow, span)?;
        Ok(result)
    }

    /// Branch to a runtime abort (never returns) when `is_overflow` is true,
    /// otherwise fall through — same branch-and-continue shape as
    /// `compile_assert` (blocks.rs). Positions the builder at the
    /// fallthrough block afterward.
    fn emit_overflow_abort_branch(
        &self,
        is_overflow: IntValue<'ctx>,
        span: Span,
    ) -> Result<(), CompileError> {
        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("checked arithmetic outside a function"))?;

        let abort_bb = self.context.append_basic_block(function, "overflow_abort");
        let pass_bb = self.context.append_basic_block(function, "overflow_pass");

        self.builder
            .build_conditional_branch(is_overflow, abort_bb, pass_bb)
            .map_err(|e| CompileError::ice(e.to_string()))?;

        self.builder.position_at_end(abort_bb);
        let message = self.overflow_message(span);
        let msg_global = self
            .builder
            .build_global_string_ptr(&message, "overflow_msg")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let msg_i64 = self
            .builder
            .build_ptr_to_int(
                msg_global.as_pointer_value(),
                self.context.i64_type(),
                "overflow_msg_i64",
            )
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let abort_fn = self
            .module
            .get_function("cantor_overflow_abort")
            .ok_or_else(|| CompileError::ice("cantor_overflow_abort not declared"))?;
        self.builder
            .build_call(abort_fn, &[msg_i64.into()], "overflow_abort_call")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        self.builder
            .build_unreachable()
            .map_err(|e| CompileError::ice(e.to_string()))?;

        self.builder.position_at_end(pass_bb);
        Ok(())
    }

    /// Format an overflow-abort message, `path:line:col`-prefixed when
    /// `overflow_ctx` is available (matches `main.rs`'s `print_compile_error`),
    /// falling back to a bare message when it isn't (`compile_items`/
    /// `compile_file` — no single coherent source string to point at).
    fn overflow_message(&self, span: Span) -> String {
        const MSG: &str = "arithmetic overflow (result does not fit in a 64-bit integer)";
        match &self.overflow_ctx {
            Some((path, src)) => {
                let (line, col) = crate::span::offset_to_line_col(src, span.start);
                format!("{path}:{line}:{col}: {MSG}")
            }
            None => MSG.to_string(),
        }
    }

    /// Value-position `rem`/`quot` — Euclidean by design (`rem` always
    /// `0 <= rem < |divisor|`), unlike `/`'s truncating-toward-zero codegen.
    /// Always a generic `SemExprKind::BinOp` node (single meaning, no
    /// Set-position dual — see `elaborate::binop`), routed here directly by
    /// `compile_expr` rather than through `compile_binop`.
    ///
    /// TODO(rem/quot BigInt support, docs/wrapping-and-quotient-sets-plan.md):
    /// no `cantor_bigint_rem`/`cantor_bigint_quot` runtime function exists
    /// yet. Rather than silently running plain-i64 Euclidean arithmetic on
    /// an operand that might actually be a boxed BigInt pointer (wrong
    /// answer, not merely unchecked), this is a hard compile error until
    /// that runtime support lands — `lk`/`rk` are already known at this
    /// point in the pipeline, so the gap is caught at compile time, not
    /// deferred to a runtime trap.
    pub(super) fn compile_rem_quot(
        &self,
        op: BinOp,
        lhs: &SemExpr,
        rhs: &SemExpr,
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (lv, lk) = self.compile_expr(lhs, env)?;
        let (rv, rk) = self.compile_expr(rhs, env)?;
        let li = self.scalarize_to_int(lv, &lk)?;
        let ri = self.scalarize_to_int(rv, &rk)?;

        if self.tagging_active() && !(lk == Kind::Int64 && rk == Kind::Int64) {
            return Err(CompileError::Unsupported {
                feature: format!(
                    "`{op}` on an Int value not proven to fit Int64 (needs \
                     cantor_bigint_rem/cantor_bigint_quot, not yet implemented)"
                ),
                span,
            });
        }

        let b = &self.builder;
        let i64_type = self.context.i64_type();
        let raw_result_kind = if self.tagging_active() {
            Kind::Int64
        } else {
            Kind::Int
        };

        // Same `i64::MIN / -1` corner `/` already guards (see `compile_arith`):
        // the truncated quotient doesn't fit in i64, and LLVM's `sdiv`/`srem`
        // are both poison at this exact operand pair. Unlike `/`, no proof
        // obligation is ever pushed for a bare `Rem` node (its result can
        // never overflow Int64 on its own), so this guard is never elided
        // for `rem` — only a `Quot` node's span can appear in
        // `overflow_checks`.
        let proved = self.overflow_checks.get(&span).copied().unwrap_or(false);
        if !proved {
            let min = i64_type.const_int(i64::MIN as u64, true);
            let neg_one = i64_type.const_all_ones();
            let is_min = b
                .build_int_compare(IntPredicate::EQ, li, min, "rq_lhs_is_min")
                .map_err(|e| CompileError::ice(e.to_string()))?;
            let is_neg_one = b
                .build_int_compare(IntPredicate::EQ, ri, neg_one, "rq_rhs_is_neg_one")
                .map_err(|e| CompileError::ice(e.to_string()))?;
            let overflow = b
                .build_and(is_min, is_neg_one, "rq_overflow")
                .map_err(|e| CompileError::ice(e.to_string()))?;
            self.emit_overflow_abort_branch(overflow, span)?;
        }

        // Truncating hardware division/remainder, then the standard
        // truncated-to-Euclidean sign correction (same transform used to
        // implement e.g. Python's `%`/`//` over hardware division):
        //   if t_rem < 0: (b > 0) ? (quot-1, rem+b) : (quot+1, rem-b)
        let t_quot = b
            .build_int_signed_div(li, ri, "tquot")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let t_rem = b
            .build_int_signed_rem(li, ri, "trem")
            .map_err(|e| CompileError::ice(e.to_string()))?;

        let zero = i64_type.const_int(0, true);
        let one = i64_type.const_int(1, true);
        let rem_neg = b
            .build_int_compare(IntPredicate::SLT, t_rem, zero, "rem_neg")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let divisor_pos = b
            .build_int_compare(IntPredicate::SGT, ri, zero, "divisor_pos")
            .map_err(|e| CompileError::ice(e.to_string()))?;

        let quot_m1 = b
            .build_int_sub(t_quot, one, "quot_m1")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let quot_p1 = b
            .build_int_add(t_quot, one, "quot_p1")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let rem_plus_b = b
            .build_int_add(t_rem, ri, "rem_plus_b")
            .map_err(|e| CompileError::ice(e.to_string()))?;
        let rem_minus_b = b
            .build_int_sub(t_rem, ri, "rem_minus_b")
            .map_err(|e| CompileError::ice(e.to_string()))?;

        let quot_if_neg = b
            .build_select(divisor_pos, quot_m1, quot_p1, "quot_if_neg")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();
        let rem_if_neg = b
            .build_select(divisor_pos, rem_plus_b, rem_minus_b, "rem_if_neg")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();

        let final_quot = b
            .build_select(rem_neg, quot_if_neg, t_quot, "final_quot")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();
        let final_rem = b
            .build_select(rem_neg, rem_if_neg, t_rem, "final_rem")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();

        let result = match op {
            BinOp::Quot => final_quot,
            BinOp::Rem => final_rem,
            _ => unreachable!("compile_rem_quot is only called for Rem/Quot"),
        };
        Ok((result.into(), raw_result_kind))
    }

    pub(super) fn compile_unop(
        &self,
        op: UnOp,
        inner: &SemExpr,
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        let (val, ty) = self.compile_expr(inner, env)?;
        let iv = self.scalarize_to_int(val, &ty)?;
        match op {
            UnOp::Neg => {
                // Signed32/Unsigned32: `sub i32 0, x` wraps correctly at
                // `i32::MIN` with no guard needed (unlike `Int`'s checked-
                // then-abort model) — this is the entire point of wrapping
                // semantics (docs/wrapping-and-quotient-sets-plan.md).
                if matches!(ty, Kind::Signed32 | Kind::Unsigned32) {
                    let zero = self.context.i32_type().const_int(0, true);
                    let v = self
                        .builder
                        .build_int_sub(zero, iv, "wneg")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    return Ok((v.into(), ty));
                }
                // int-soundness-plan phase 3 step 4b: a tagged `Kind::Int`
                // operand routes through `cantor_bigint_neg` (never
                // overflows, promotes to boxed `BigInt` internally instead);
                // only a genuinely raw `Kind::Int64` operand stays on phase
                // 1's checked-i64 path below.
                if self.tagging_active() && ty != Kind::Int64 {
                    let iv = self.ensure_tagged(iv, &ty)?;
                    let neg_fn = self
                        .module
                        .get_function("cantor_bigint_neg")
                        .ok_or_else(|| CompileError::ice("cantor_bigint_neg not declared"))?;
                    let result = self
                        .builder
                        .build_call(neg_fn, &[iv.into()], "bigint_neg")
                        .map_err(|e| CompileError::ice(e.to_string()))?
                        .try_as_basic_value()
                        .left()
                        .ok_or_else(|| CompileError::ice("cantor_bigint_neg returned void"))?;
                    return Ok((result, Kind::Int));
                }
                // int-soundness-plan phase 1: `-x` overflows only at `i64::MIN`.
                // Lowered as `0 - x` via `ssub.with.overflow` when unproved so
                // it shares `emit_checked_arith_i64` with `Sub` rather than a
                // bespoke compare.
                let raw_result_kind = if self.tagging_active() {
                    Kind::Int64
                } else {
                    Kind::Int
                };
                if self.overflow_checks.get(&span).copied().unwrap_or(false) {
                    let v = self
                        .builder
                        .build_int_neg(iv, "neg")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    return Ok((v.into(), raw_result_kind));
                }
                let zero = self.context.i64_type().const_int(0, true);
                let v = self.emit_checked_arith_i64("llvm.ssub.with.overflow", zero, iv, span)?;
                Ok((v.into(), raw_result_kind))
            }
            // build_not is bitwise NOT; on i1 this is logical NOT (0↔1).
            UnOp::Not => {
                let v = self
                    .builder
                    .build_not(iv, "not")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                Ok((v.into(), Kind::Bool))
            }
        }
    }
}
