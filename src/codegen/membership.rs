use inkwell::{IntPredicate, values::{BasicValueEnum, IntValue}};

use crate::{
    ast::{BinOp, Expr, ExprKind},
    error::CompileError,
    kind::{Kind, SetElemKind},
};

use super::Compiler;

impl<'ctx> Compiler<'ctx> {
    /// Compile `val ∈ set_expr` to an `i1` LLVM predicate.
    ///
    /// Mirrors `membership_constraint` in the solver but emits LLVM IR instead
    /// of cvc5 terms.  The same named sets are supported: Int, Nat, NatPos,
    /// NonZeroInt, Int8/16/32/64, set literals, and set union/difference/intersection.
    pub(in crate::codegen) fn compile_membership(
        &self,
        val: IntValue<'ctx>,
        set_expr: &Expr,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let b    = &self.builder;
        let i64  = self.context.i64_type();
        let bool = self.context.bool_type();

        match &set_expr.kind {
            ExprKind::Var(sym) => match sym.0.as_str() {
                "Int"       => Ok(bool.const_int(1, false)),
                "Nat"       => b
                    .build_int_compare(IntPredicate::SGE, val, i64.const_int(0, true), "in_nat")
                    .map_err(|e| CompileError::Internal(e.to_string())),
                "NatPos"    => b
                    .build_int_compare(IntPredicate::SGT, val, i64.const_int(0, true), "in_natpos")
                    .map_err(|e| CompileError::Internal(e.to_string())),
                "NonZeroInt" => b
                    .build_int_compare(IntPredicate::NE, val, i64.const_int(0, true), "in_nonzero")
                    .map_err(|e| CompileError::Internal(e.to_string())),
                "Fail"  => Ok(bool.const_int(0, false)),
                // Bool values are represented as i1 (0/1) at runtime.  A value
                // is in Bool iff it is 0 or 1 as an i64.  Normalise i1 to i64
                // first so the integer comparisons below are well-typed.
                "Bool"  => {
                    let val_i64 = if val.get_type().get_bit_width() == 1 {
                        self.builder
                            .build_int_z_extend(val, i64, "bool_to_i64_mem")
                            .map_err(|e| CompileError::Internal(e.to_string()))?
                    } else {
                        val
                    };
                    let zero = i64.const_int(0, false);
                    let one  = i64.const_int(1, false);
                    let eq0 = b.build_int_compare(IntPredicate::EQ, val_i64, zero, "bool_eq0")
                        .map_err(|e| CompileError::Internal(e.to_string()))?;
                    let eq1 = b.build_int_compare(IntPredicate::EQ, val_i64, one, "bool_eq1")
                        .map_err(|e| CompileError::Internal(e.to_string()))?;
                    b.build_or(eq0, eq1, "in_bool")
                        .map_err(|e| CompileError::Internal(e.to_string()))
                }
                "Int8"  => self.compile_bounded_membership(val, i8::MIN  as i64, i8::MAX  as i64),
                "Int16" => self.compile_bounded_membership(val, i16::MIN as i64, i16::MAX as i64),
                "Int32" => self.compile_bounded_membership(val, i32::MIN as i64, i32::MAX as i64),
                "Int64" => self.compile_bounded_membership(val, i64::MIN,        i64::MAX        ),
                other => {
                    // Check user-defined named sets (e.g. `HTTPError = {400, 503}`).
                    if let Some(vals) = self.user_set_vals.get(other) {
                        self.build_int_set_membership(val, vals)
                    } else {
                        Err(CompileError::Internal(format!("unknown set `{other}`")))
                    }
                }
            },

            ExprKind::SetLit(elements) => {
                if elements.is_empty() {
                    return Ok(bool.const_int(0, false));
                }
                let mut acc: Option<IntValue<'ctx>> = None;
                for elem in elements {
                    let ExprKind::IntLit(n) = &elem.kind else {
                        return Err(CompileError::Internal("non-literal in set literal".into()));
                    };
                    let elem_val = i64.const_int(*n as u64, true);
                    let eq = b
                        .build_int_compare(IntPredicate::EQ, val, elem_val, "set_eq")
                        .map_err(|e| CompileError::Internal(e.to_string()))?;
                    acc = Some(match acc {
                        None       => eq,
                        Some(prev) => b
                            .build_or(prev, eq, "set_or")
                            .map_err(|e| CompileError::Internal(e.to_string()))?,
                    });
                }
                Ok(acc.unwrap())
            }

            // t ∈ A - B  →  (t ∈ A) && !(t ∈ B)
            ExprKind::BinOp { op: BinOp::Sub, lhs, rhs } => {
                let in_a  = self.compile_membership(val, lhs)?;
                let in_b  = self.compile_membership(val, rhs)?;
                let not_b = b.build_not(in_b, "not_b")
                    .map_err(|e| CompileError::Internal(e.to_string()))?;
                b.build_and(in_a, not_b, "set_diff")
                    .map_err(|e| CompileError::Internal(e.to_string()))
            }

            // t ∈ A | B  →  (t ∈ A) || (t ∈ B)
            ExprKind::BinOp { op: BinOp::Union, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                b.build_or(in_a, in_b, "set_union")
                    .map_err(|e| CompileError::Internal(e.to_string()))
            }

            // t ∈ A + B  →  (t ∈ A) || (t ∈ B)  (disjointness is proved statically)
            ExprKind::BinOp { op: BinOp::Add, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                b.build_or(in_a, in_b, "djunion_mem")
                    .map_err(|e| CompileError::Internal(e.to_string()))
            }

            // t ∈ A & B  →  (t ∈ A) && (t ∈ B)
            ExprKind::BinOp { op: BinOp::Intersect, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                b.build_and(in_a, in_b, "set_inter")
                    .map_err(|e| CompileError::Internal(e.to_string()))
            }

            // t ∈ A ^ B  →  (t ∈ A) XOR (t ∈ B)  =  (a || b) && !(a && b)
            ExprKind::BinOp { op: BinOp::SymDiff, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                let or_ab  = b.build_or (in_a, in_b, "symdiff_or" ).map_err(|e| CompileError::Internal(e.to_string()))?;
                let and_ab = b.build_and(in_a, in_b, "symdiff_and").map_err(|e| CompileError::Internal(e.to_string()))?;
                let not_and = b.build_not(and_ab, "symdiff_not").map_err(|e| CompileError::Internal(e.to_string()))?;
                b.build_and(or_ab, not_and, "symdiff_xor")
                    .map_err(|e| CompileError::Internal(e.to_string()))
            }

            _ => Err(CompileError::Internal(
                "unsupported set expression in membership check".into(),
            )),
        }
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
            SetElemKind::Int  => "cantor_set_contains_i64",
            SetElemKind::Bool => "cantor_set_contains_bool",
        };
        let fn_val = self.module.get_function(contains_fn)
            .ok_or_else(|| CompileError::Internal(format!("{contains_fn} not declared")))?;
        let val_i64: BasicValueEnum = if val_kind == Kind::Bool {
            self.builder
                .build_int_z_extend(val.into_int_value(), i64t, "val_bool_ext")
                .map_err(|e| CompileError::Internal(e.to_string()))?
                .into()
        } else {
            val
        };
        let result_i64 = self.builder
            .build_call(fn_val, &[set_ptr.into(), val_i64.into()], "contains")
            .map_err(|e| CompileError::Internal(e.to_string()))?
            .try_as_basic_value().left()
            .ok_or_else(|| CompileError::Internal("contains fn returned void".into()))?
            .into_int_value();
        // Truncate the i64 0/1 result to i1 to match compile_membership's return shape.
        self.builder
            .build_int_truncate(result_i64, self.context.bool_type(), "contains_i1")
            .map_err(|e| CompileError::Internal(e.to_string()))
    }

    /// Emit `val == v0 || val == v1 || …` as an `i1` predicate.
    ///
    /// Used by `compile_try` to check whether a call result is a member of a
    /// named error set (e.g. `{400, 503}`) at runtime.
    pub(in crate::codegen) fn build_int_set_membership(
        &self,
        val: IntValue<'ctx>,
        values: &[i64],
    ) -> Result<IntValue<'ctx>, CompileError> {
        if values.is_empty() {
            return Ok(self.context.bool_type().const_int(0, false));
        }
        let b = &self.builder;
        let i64t = self.context.i64_type();
        let mut acc: Option<IntValue<'ctx>> = None;
        for &n in values {
            let n_val = i64t.const_int(n as u64, true);
            let eq = b
                .build_int_compare(IntPredicate::EQ, val, n_val, "err_eq")
                .map_err(|e| CompileError::Internal(e.to_string()))?;
            acc = Some(match acc {
                None => eq,
                Some(prev) => b
                    .build_or(prev, eq, "err_or")
                    .map_err(|e| CompileError::Internal(e.to_string()))?,
            });
        }
        Ok(acc.unwrap())
    }

    fn compile_bounded_membership(
        &self,
        val: IntValue<'ctx>,
        min: i64,
        max: i64,
    ) -> Result<IntValue<'ctx>, CompileError> {
        let b   = &self.builder;
        let i64 = self.context.i64_type();
        let lo  = i64.const_int(min as u64, true);
        let hi  = i64.const_int(max as u64, true);
        let ge  = b
            .build_int_compare(IntPredicate::SGE, val, lo, "ge")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        let le  = b
            .build_int_compare(IntPredicate::SLE, val, hi, "le")
            .map_err(|e| CompileError::Internal(e.to_string()))?;
        b.build_and(ge, le, "bounded")
            .map_err(|e| CompileError::Internal(e.to_string()))
    }
}
