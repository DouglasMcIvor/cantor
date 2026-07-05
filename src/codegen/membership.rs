use inkwell::{
    IntPredicate,
    values::{BasicValueEnum, IntValue},
};

use crate::{
    ast::BinOp,
    error::CompileError,
    kind::{Kind, SetElemKind},
    semantics::builtins::{self, IntBound},
    semantics::tree::{SemExpr, SemExprKind},
};

use super::Compiler;

impl<'ctx> Compiler<'ctx> {
    /// Compile `val ∈ set_expr` to an `i1` LLVM predicate.
    ///
    /// Mirrors `membership_constraint` in the solver but emits LLVM IR instead
    /// of cvc5 terms.  The same named sets are supported: Int, Nat, NatPos,
    /// NonZeroInt, Int8/16/32/64, set literals, and set union/difference/intersection.
    ///
    /// `tagged` — int-soundness-plan phase 3 step 4b — must be `true` when
    /// `val` is a tagged `Kind::Int` word (small-or-boxed, see
    /// `runtime/mod.rs`'s module doc) rather than a raw `Kind::Int64` one;
    /// every bound/equality check below needs to know which, since a tagged
    /// small value's *bit pattern* isn't the same as its integer value (it's
    /// shifted), and a boxed value's bit pattern isn't even numeric (it's a
    /// pointer) — a raw comparison against an unshifted constant is wrong in
    /// both cases. Threaded through unchanged across every recursive call
    /// (the same `val` is being checked throughout one membership tree).
    pub(in crate::codegen) fn compile_membership(
        &self,
        val: IntValue<'ctx>,
        set_expr: &SemExpr,
        tagged: bool,
    ) -> Result<IntValue<'ctx>, CompileError> {
        // int-soundness-plan phase 3 step 4b: force `false` outside the
        // solver-verified pipeline (see `Compiler::tagging_active`'s doc
        // comment) — a caller's `lk == Kind::Int` check can't tell the
        // difference on its own, since `Kind::Int` means the same thing
        // (tagged, once verified; plain, otherwise) either way.
        let tagged = tagged && self.tagging_active();
        let b = &self.builder;
        let i64 = self.context.i64_type();
        let bool = self.context.bool_type();

        match &set_expr.kind {
            SemExprKind::Var(sym) => match builtins::lookup(&sym.0) {
                Some(builtin) if builtin.kind == Kind::Fail => Ok(bool.const_int(0, false)),
                // Bool values are represented as i1 (0/1) at runtime.  A value
                // is in Bool iff it is 0 or 1 as an i64.  Normalise i1 to i64
                // first so the integer comparisons below are well-typed.
                // Never tagged — Bool is never an Int/Int64 position.
                Some(builtin) if builtin.kind == Kind::Bool => {
                    let val_i64 = if val.get_type().get_bit_width() == 1 {
                        self.builder
                            .build_int_z_extend(val, i64, "bool_to_i64_mem")
                            .map_err(|e| CompileError::ice(e.to_string()))?
                    } else {
                        val
                    };
                    let zero = i64.const_int(0, false);
                    let one = i64.const_int(1, false);
                    let eq0 = b
                        .build_int_compare(IntPredicate::EQ, val_i64, zero, "bool_eq0")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let eq1 = b
                        .build_int_compare(IntPredicate::EQ, val_i64, one, "bool_eq1")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    b.build_or(eq0, eq1, "in_bool")
                        .map_err(|e| CompileError::ice(e.to_string()))
                }
                Some(builtin) => match builtin.bound {
                    IntBound::Any => Ok(bool.const_int(1, false)),
                    IntBound::NonNeg => {
                        self.compile_int_cmp_const(val, 0, IntPredicate::SGE, tagged)
                    }
                    IntBound::Positive => {
                        self.compile_int_cmp_const(val, 0, IntPredicate::SGT, tagged)
                    }
                    IntBound::NonZero => {
                        self.compile_int_cmp_const(val, 0, IntPredicate::NE, tagged)
                    }
                    IntBound::Bounded(min, max) => {
                        self.compile_bounded_membership(val, min, max, tagged)
                    }
                    IntBound::Outside(min, max) => {
                        self.compile_outside_membership(val, min, max, tagged)
                    }
                },
                None => {
                    // Check user-defined named sets (e.g. `HTTPError = {400, 503}`).
                    if let Some(vals) = self.user_set_vals.get(sym.0.as_str()) {
                        self.build_int_set_membership(val, vals, tagged)
                    } else {
                        Err(CompileError::ice(format!("unknown set `{}`", sym.0)))
                    }
                }
            },

            SemExprKind::SetLit(elements) => {
                let vals: Vec<i64> = elements
                    .iter()
                    .map(|elem| match &elem.kind {
                        SemExprKind::IntLit(n) => Ok(*n),
                        _ => Err(CompileError::ice("non-literal in set literal")),
                    })
                    .collect::<Result<_, _>>()?;
                self.build_int_set_membership(val, &vals, tagged)
            }

            // t ∈ A - B  →  (t ∈ A) && !(t ∈ B)
            SemExprKind::SetDifference(lhs, rhs) => {
                let in_a = self.compile_membership(val, lhs, tagged)?;
                let in_b = self.compile_membership(val, rhs, tagged)?;
                let not_b = b
                    .build_not(in_b, "not_b")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                b.build_and(in_a, not_b, "set_diff")
                    .map_err(|e| CompileError::ice(e.to_string()))
            }

            // t ∈ A | B  →  (t ∈ A) || (t ∈ B)
            SemExprKind::BinOp {
                op: BinOp::Union,
                lhs,
                rhs,
            } => {
                let in_a = self.compile_membership(val, lhs, tagged)?;
                let in_b = self.compile_membership(val, rhs, tagged)?;
                b.build_or(in_a, in_b, "set_union")
                    .map_err(|e| CompileError::ice(e.to_string()))
            }

            // t ∈ A + B  →  (t ∈ A) || (t ∈ B)  (disjointness is proved statically)
            SemExprKind::DisjointUnion(lhs, rhs) => {
                let in_a = self.compile_membership(val, lhs, tagged)?;
                let in_b = self.compile_membership(val, rhs, tagged)?;
                b.build_or(in_a, in_b, "djunion_mem")
                    .map_err(|e| CompileError::ice(e.to_string()))
            }

            // t ∈ A & B  →  (t ∈ A) && (t ∈ B)
            SemExprKind::BinOp {
                op: BinOp::Intersect,
                lhs,
                rhs,
            } => {
                let in_a = self.compile_membership(val, lhs, tagged)?;
                let in_b = self.compile_membership(val, rhs, tagged)?;
                b.build_and(in_a, in_b, "set_inter")
                    .map_err(|e| CompileError::ice(e.to_string()))
            }

            // t ∈ A ^ B  →  (t ∈ A) XOR (t ∈ B)  =  (a || b) && !(a && b)
            SemExprKind::BinOp {
                op: BinOp::SymDiff,
                lhs,
                rhs,
            } => {
                let in_a = self.compile_membership(val, lhs, tagged)?;
                let in_b = self.compile_membership(val, rhs, tagged)?;
                let or_ab = b
                    .build_or(in_a, in_b, "symdiff_or")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let and_ab = b
                    .build_and(in_a, in_b, "symdiff_and")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                let not_and = b
                    .build_not(and_ab, "symdiff_not")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                b.build_and(or_ab, not_and, "symdiff_xor")
                    .map_err(|e| CompileError::ice(e.to_string()))
            }

            _ => Err(CompileError::ice(
                "unsupported set expression in membership check",
            )),
        }
    }

    /// Compare `val` against the compile-time constant `k` using `predicate`
    /// — correct whether `val` is a raw `Int64` word (`tagged = false`, a
    /// plain `icmp`) or a tagged `Int` word (`tagged = true`): a *small*
    /// tagged value's order relative to another value is preserved exactly
    /// by the `<< 1` encoding (comparing both operands shifted the same way
    /// preserves `<`/`=`/`>`), but a *boxed* value's raw bit pattern is a
    /// pointer, not a number — so the tagged case also computes the boxed
    /// answer via `cantor_bigint_cmp` and `select`s between the two based on
    /// the tag bit. Always computes both (a `select`, not a branch) since
    /// this is only ever reached on an already-not-statically-elided
    /// membership check, not phase 1's zero-cost proved-arithmetic path.
    fn compile_int_cmp_const(
        &self,
        val: IntValue<'ctx>,
        k: i64,
        predicate: IntPredicate,
        tagged: bool,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let i64t = self.context.i64_type();
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        if !tagged {
            return self
                .builder
                .build_int_compare(predicate, val, i64t.const_int(k as u64, true), "cmp_const")
                .map_err(err);
        }

        let tagged_k = self.compile_tagged_i64_const(k)?;
        let small_result = self
            .builder
            .build_int_compare(predicate, val, tagged_k, "cmp_const_small")
            .map_err(err)?;

        let cmp_fn = self
            .module
            .get_function("cantor_bigint_cmp")
            .ok_or_else(|| CompileError::ice("cantor_bigint_cmp not declared"))?;
        let cmp = self
            .builder
            .build_call(cmp_fn, &[val.into(), tagged_k.into()], "cmp_const_box")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_bigint_cmp returned void"))?
            .into_int_value();
        let zero = i64t.const_int(0, true);
        let boxed_result = self
            .builder
            .build_int_compare(predicate, cmp, zero, "cmp_const_boxed")
            .map_err(err)?;

        let one = i64t.const_int(1, false);
        let tag_bit = self.builder.build_and(val, one, "tag_bit").map_err(err)?;
        let is_boxed = self
            .builder
            .build_int_compare(IntPredicate::EQ, tag_bit, one, "is_boxed")
            .map_err(err)?;
        self.builder
            .build_select(is_boxed, boxed_result, small_result, "cmp_const_sel")
            .map_err(err)
            .map(|v| v.into_int_value())
    }

    /// Emit a tag check for `val ∈ set_expr` where `val : TaggedUnion(arms)`.
    ///
    /// Finds the arm index whose Kind matches `set_kind(set_expr)` and returns
    /// `(tag == arm_idx) as i1`.  Only supports set expressions that exactly match
    /// one arm by kind; anything more complex returns a compile error.
    pub(in crate::codegen) fn compile_tagged_union_membership(
        &self,
        val: BasicValueEnum<'ctx>,
        arms: &[Kind],
        set_expr: &SemExpr,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let target_kind = &set_expr.kind_of;
        let arm_idx = arms.iter().position(|k| k == target_kind).ok_or_else(|| {
            CompileError::ice(format!(
                "tagged-union membership: set expression kind {target_kind:?} \
                 does not match any arm in {arms:?}"
            ))
        })?;

        let struct_val = val.into_struct_value();
        let tag = self
            .builder
            .build_extract_value(struct_val, 0, "tu_tag")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .into_int_value();

        // Widen i32 tag to i64 for comparison.
        let tag_i64 = self
            .builder
            .build_int_z_extend(tag, self.context.i64_type(), "tu_tag64")
            .map_err(|e| CompileError::ice(e.to_string()))?;

        let expected = self.context.i64_type().const_int(arm_idx as u64, false);
        self.builder
            .build_int_compare(IntPredicate::EQ, tag_i64, expected, "tu_arm_eq")
            .map_err(|e| CompileError::ice(e.to_string()))
    }

    /// Emit a `cantor_set_contains_*` call for `val ∈ runtime_set`.
    ///
    /// Returns an `i1` (true/false), matching the shape of `compile_membership`.
    /// Bool values are widened to i64 before the call (uniform ABI).
    pub(in crate::codegen) fn compile_runtime_contains(
        &self,
        val: BasicValueEnum<'ctx>,
        val_kind: Kind,
        set_ptr: BasicValueEnum<'ctx>,
        elem_kind: SetElemKind,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let i64t = self.context.i64_type();
        let contains_fn = match elem_kind {
            SetElemKind::Int => "cantor_set_contains_i64",
            SetElemKind::Bool => "cantor_set_contains_bool",
        };
        let fn_val = self
            .module
            .get_function(contains_fn)
            .ok_or_else(|| CompileError::ice(format!("{contains_fn} not declared")))?;
        // int-soundness-plan phase 3 step 4b: runtime `Set(Int)` storage is
        // out of scope for tagging in this pass (see docs/int-soundness-plan.md) —
        // it stores plain raw i64 elements exactly as before, so a tagged
        // `Kind::Int` value must be decoded first. Sound because
        // `ensure_raw_int64` aborts loudly (never silently truncates) if the
        // value doesn't actually fit, rather than corrupting set membership —
        // TODO: the abort message it uses ("compiler invariant violated") is
        // written for the call-boundary use case, where not-fitting really
        // would mean a compiler bug; here a genuinely-huge value hitting an
        // unsupported `Set(Int)` isn't a compiler bug, just an unimplemented
        // feature, and deserves its own clearer message if this becomes a
        // real usability complaint.
        let val_i64: BasicValueEnum = if val_kind == Kind::Bool {
            self.builder
                .build_int_z_extend(val.into_int_value(), i64t, "val_bool_ext")
                .map_err(|e| CompileError::ice(e.to_string()))?
                .into()
        } else if val_kind == Kind::Int {
            self.ensure_raw_int64(val.into_int_value(), &val_kind)?
                .into()
        } else {
            val
        };
        let result_i64 = self
            .builder
            .build_call(fn_val, &[set_ptr.into(), val_i64.into()], "contains")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("contains fn returned void"))?
            .into_int_value();
        // Truncate the i64 0/1 result to i1 to match compile_membership's return shape.
        self.builder
            .build_int_truncate(result_i64, self.context.bool_type(), "contains_i1")
            .map_err(|e| CompileError::ice(e.to_string()))
    }

    /// Emit `val == v0 || val == v1 || …` as an `i1` predicate.
    ///
    /// Used by `compile_membership` for both user-defined named integer sets
    /// (e.g. `x in HTTPError` where `HTTPError = {400, 503}`) and set
    /// literals (`x in {1, 2, 3}`). `tagged` — see `compile_membership`'s
    /// doc comment — is threaded through unchanged from the caller.
    pub(in crate::codegen) fn build_int_set_membership(
        &self,
        val: IntValue<'ctx>,
        values: &[i64],
        tagged: bool,
    ) -> Result<IntValue<'ctx>, CompileError> {
        if values.is_empty() {
            return Ok(self.context.bool_type().const_int(0, false));
        }
        let b = &self.builder;
        let mut acc: Option<IntValue<'ctx>> = None;
        for &n in values {
            let eq = self.compile_int_cmp_const(val, n, IntPredicate::EQ, tagged)?;
            acc = Some(match acc {
                None => eq,
                Some(prev) => b
                    .build_or(prev, eq, "err_or")
                    .map_err(|e| CompileError::ice(e.to_string()))?,
            });
        }
        Ok(acc.unwrap())
    }

    fn compile_bounded_membership(
        &self,
        val: IntValue<'ctx>,
        min: i64,
        max: i64,
        tagged: bool,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let ge = self.compile_int_cmp_const(val, min, IntPredicate::SGE, tagged)?;
        let le = self.compile_int_cmp_const(val, max, IntPredicate::SLE, tagged)?;
        self.builder
            .build_and(ge, le, "bounded")
            .map_err(|e| CompileError::ice(e.to_string()))
    }

    /// The complement of [`Self::compile_bounded_membership`]: `val < min ||
    /// val > max` — currently only reached via `BigInt = Int - Int64`
    /// (`Outside(i64::MIN, i64::MAX)`).
    fn compile_outside_membership(
        &self,
        val: IntValue<'ctx>,
        min: i64,
        max: i64,
        tagged: bool,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let lt = self.compile_int_cmp_const(val, min, IntPredicate::SLT, tagged)?;
        let gt = self.compile_int_cmp_const(val, max, IntPredicate::SGT, tagged)?;
        self.builder
            .build_or(lt, gt, "outside")
            .map_err(|e| CompileError::ice(e.to_string()))
    }
}
