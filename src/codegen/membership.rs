use inkwell::{IntPredicate, values::IntValue};

use crate::{
    ast::{BinOp, Expr, ExprKind},
    error::CompileError,
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
                other   => Err(CompileError::Internal(format!("unknown set `{other}`"))),
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

            // t ∈ A & B  →  (t ∈ A) && (t ∈ B)
            ExprKind::BinOp { op: BinOp::Intersect, lhs, rhs } => {
                let in_a = self.compile_membership(val, lhs)?;
                let in_b = self.compile_membership(val, rhs)?;
                b.build_and(in_a, in_b, "set_inter")
                    .map_err(|e| CompileError::Internal(e.to_string()))
            }

            _ => Err(CompileError::Internal(
                "unsupported set expression in membership check".into(),
            )),
        }
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
