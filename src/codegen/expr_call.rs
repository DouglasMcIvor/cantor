use inkwell::values::BasicValueEnum;

use crate::{
    error::CompileError,
    kind::Kind,
    semantics::tree::SemExpr,
    span::{Span, Symbol},
};

use super::expr_vec::vector_len_fn_name;
use super::overload_dispatch::CallTarget;
use super::{Compiler, Env};

impl<'ctx> Compiler<'ctx> {
    pub(super) fn compile_call(
        &self,
        callee: &Symbol,
        args: &[SemExpr],
        env: &Env<'ctx>,
        span: Span,
    ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError> {
        // `from(x)` — built-in destructor. Identity at runtime for `distinct`
        // values (preserves the argument's actual Kind, Int or Int64,
        // whichever it already is — a pure pass-through, not a fresh value).
        // For a Signed32/Unsigned32/Char argument (docs/wrapping-and-
        // quotient-sets-plan.md, docs/design-decisions.md §13) it's
        // genuinely not identity: sign-/zero-extend the i32 register up to
        // i64, then tag it (a raw i64 straight from a 32-bit register always
        // fits `Int64`, so `ensure_tagged` is always sound here, never the
        // boxed-BigInt path) to produce a proper `Kind::Int` value — the
        // wire type `Kind::Int` always means tagged.
        if callee.0 == "from" && args.len() == 1 {
            let (val, kind) = self.compile_expr(&args[0], env)?;
            if matches!(kind, Kind::Signed32 | Kind::Unsigned32 | Kind::Char) {
                let i64t = self.context.i64_type();
                let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
                // Char is always zero-extended, same as Unsigned32 — codepoints
                // are non-negative.
                let wide = if kind == Kind::Signed32 {
                    self.builder
                        .build_int_s_extend(val.into_int_value(), i64t, "from_s32")
                } else {
                    self.builder
                        .build_int_z_extend(val.into_int_value(), i64t, "from_u32")
                }
                .map_err(err)?;
                let tagged = self.ensure_tagged(wide, &Kind::Int64)?;
                return Ok((tagged.into(), Kind::Int));
            }
            return Ok((val, kind));
        }

        // Auto-generated constructor `char(n)` for the builtin `Char`
        // distinct sort (docs/design-decisions.md §13). Checked *before* the
        // `distinct_names` identity path below (which would otherwise treat
        // `char` as an ordinary user `distinct` constructor and wrongly pass
        // the argument through unchanged) — same reasoning as checking
        // Signed32/Unsigned32 first. No runtime range-check needed here:
        // unlike `assert`, a `BuiltinObligation` that can't be proved makes
        // the whole file fail to compile (`check_file` reports it as a
        // counterexample/unknown and codegen never runs) — same guarantee
        // `litre(n)`'s basis obligation already relies on. By the time this
        // code runs, every `char(n)` call site's argument is already proved
        // valid, so a plain untag + truncate is sound, exactly like
        // `signed32(n)`/`unsigned32(n)` below.
        if callee.0 == "char" && args.len() == 1 {
            let (val, arg_kind) = self.compile_expr(&args[0], env)?;
            let raw = self.ensure_raw_int64(val.into_int_value(), &arg_kind)?;
            let i32t = self.context.i32_type();
            let truncated = self
                .builder
                .build_int_truncate(raw, i32t, "char_ctor")
                .map_err(|e| CompileError::ice(e.to_string()))?;
            return Ok((truncated.into(), Kind::Char));
        }

        // Auto-generated constructor `Name.Label(x)` for a named union arm
        // (`Name = distinct (Label: Expr | ...)`); identity at runtime, same
        // as the plain single-basis `d(x)` case just below — v0 named
        // unions are Int-only (`semantics::elaborate::elaborate_name_def`
        // rejects non-Int arms), so there's no tag/struct to build, just
        // the same pass-through `distinct` already does. The label itself
        // carries no runtime information; only `Name` needs to be a known
        // distinct set.
        if args.len() == 1
            && let Some((name_part, _label_part)) = callee.0.split_once('.')
            && self.distinct_names.contains(name_part)
        {
            let (val, kind) = self.compile_expr(&args[0], env)?;
            return Ok((val, kind));
        }

        // Auto-generated constructor `d(x)` for `D = distinct B`; identity at
        // runtime — same reasoning as `from(x)` above.
        if args.len() == 1 {
            let mut chars = callee.0.chars();
            if let Some(first) = chars.next() {
                let capitalized = first.to_uppercase().collect::<String>() + chars.as_str();
                if self.distinct_names.contains(&capitalized) {
                    let (val, kind) = self.compile_expr(&args[0], env)?;
                    return Ok((val, kind));
                }
                // Auto-generated constructor `signed32(n)`/`unsigned32(n)`
                // (docs/wrapping-and-quotient-sets-plan.md): untag the `Int`
                // argument first (it may be the tagged small-int/boxed-BigInt
                // representation, not a raw i64 — same concern
                // `int64_split`'s promotion machinery already handles via
                // `ensure_raw_int64`), then reduce to the i32 register via a
                // plain `trunc`. Total — unlike `distinct`'s constructor
                // there's no basis obligation, so nothing else to emit.
                if capitalized == "Signed32" || capitalized == "Unsigned32" {
                    let (val, arg_kind) = self.compile_expr(&args[0], env)?;
                    let raw = self.ensure_raw_int64(val.into_int_value(), &arg_kind)?;
                    let i32t = self.context.i32_type();
                    let truncated = self
                        .builder
                        .build_int_truncate(raw, i32t, "wrap_ctor")
                        .map_err(|e| CompileError::ice(e.to_string()))?;
                    let result_kind = if capitalized == "Signed32" {
                        Kind::Signed32
                    } else {
                        Kind::Unsigned32
                    };
                    return Ok((truncated.into(), result_kind));
                }
            }
        }

        // `size(s)` — built-in cardinality function for runtime sets.
        if callee.0 == "size" && args.len() == 1 {
            let (ptr, kind) = self.compile_expr(&args[0], env)?;
            let size_fn = match &kind {
                // Cardinality is representation-agnostic (every backing
                // struct is a plain `Vec<i64>` under the hood, tagged or
                // not), so the raw-vs-tagged split that `contains`/`for`
                // need doesn't matter here.
                Kind::Set(elem) if **elem == Kind::Bool => "cantor_set_size_bool",
                Kind::Set(_) => "cantor_set_size_i64",
                _ => return Err(CompileError::ice("size() requires a runtime set argument")),
            };
            let fn_val = self
                .module
                .get_function(size_fn)
                .ok_or_else(|| CompileError::ice(format!("{size_fn} not declared")))?;
            let result = self
                .builder
                .build_call(fn_val, &[ptr.into()], "size")
                .map_err(|e| CompileError::ice(e.to_string()))?
                .try_as_basic_value()
                .left()
                .ok_or_else(|| CompileError::ice("size fn returned void"))?;
            // int-soundness-plan phase 3 step 4b: `cantor_set_size_i64`
            // returns a raw i64 count, but this builtin's result is an
            // ordinary `Kind::Int` (tagged) value like any other — tag it.
            let result = self
                .ensure_tagged(result.into_int_value(), &Kind::Int64)?
                .into();
            return Ok((result, Kind::Int));
        }

        // `len(xs)` — built-in length function for vectors (Kind::Vector).
        if callee.0 == "len" && args.len() == 1 {
            let (ptr, kind) = self.compile_expr(&args[0], env)?;
            return match &kind {
                Kind::Vector(ek) => {
                    let len_fn = vector_len_fn_name(ek)?;

                    let fn_val = self
                        .module
                        .get_function(len_fn)
                        .ok_or_else(|| CompileError::ice(format!("{len_fn} not declared")))?;
                    let result = self
                        .builder
                        .build_call(fn_val, &[ptr.into()], "len")
                        .map_err(|e| CompileError::ice(e.to_string()))?
                        .try_as_basic_value()
                        .left()
                        .ok_or_else(|| CompileError::ice("len fn returned void"))?;
                    // int-soundness-plan phase 3 step 4b: same reasoning as
                    // `size()` above — the runtime function returns a raw
                    // count, tag it before it's used as a `Kind::Int` value.
                    let result = self
                        .ensure_tagged(result.into_int_value(), &Kind::Int64)?
                        .into();
                    Ok((result, Kind::Int))
                }
                Kind::Tuple(inner_eks) => {
                    let length = Vec::len(inner_eks);
                    let v = self.compile_tagged_i64_const(length as i64)?;
                    Ok((v.into(), Kind::Int))
                }
                _ => Err(CompileError::ice("len() requires a vector (X*) argument")),
            };
        }

        // `show(x)` — builtin display conversion, any Kind to `Char*`.
        // Backs string interpolation (`parser::expr`'s `desugar_interp_parts`
        // desugars each `{expr}` chunk to `show(expr)`), also directly
        // callable. Per-Kind logic lives in `codegen::show`.
        if callee.0 == "show" && args.len() == 1 {
            let (val, kind) = self.compile_expr(&args[0], env)?;
            let result = self.compile_show(&kind, val, span)?;
            return Ok((result, Kind::Vector(Box::new(Kind::Char))));
        }

        // int-soundness-plan phase 2: overload dispatch. Absent from
        // `overload_dispatch` ⇒ today's plain path, unchanged (the
        // overwhelming common case). Present ⇒ resolve which candidate(s)
        // this call's arity admits, then either a direct call (arity alone,
        // or a solver-proved resolution, picked exactly one) or a runtime
        // membership-test dispatch chain.
        let (lookup_key, target) = self.resolve_overload_call_target(callee, args, span)?;

        // int-soundness-plan phase 3 step 4b: an unresolved dispatch call
        // must present every candidate a *common* representation to test
        // membership against and to `phi`-merge results from — that common
        // representation is the tagged `Kind::Int` (never raw `Kind::Int64`,
        // which has no tag bit to represent "whichever candidate wins"
        // generically). `lookup_key`'s own declared kinds might be the
        // `Int64` half of a compiler-generated split (file order pushes it
        // first), so a real `Direct` call still uses the callee's exact
        // declared kinds unchanged, but a `Dispatch` call canonicalizes any
        // `Int64` position to `Int` here — `compile_overload_dispatch`
        // decodes back down to each individual candidate's real kind right
        // before calling it.
        let param_kinds_for_callee = self.fn_param_kinds.get(&lookup_key).map(|ks| {
            if matches!(target, CallTarget::Dispatch(_)) {
                ks.iter()
                    .map(|k| {
                        if *k == Kind::Int64 {
                            Kind::Int
                        } else {
                            k.clone()
                        }
                    })
                    .collect()
            } else {
                ks.clone()
            }
        });
        let mut compiled_arg_values = Vec::with_capacity(args.len());
        for (arg_idx, arg) in args.iter().enumerate() {
            let (v, arg_kind) = self.compile_expr(arg, env)?;
            let expected_kind = param_kinds_for_callee
                .as_deref()
                .and_then(|ks| ks.get(arg_idx));

            // When the callee expects a Vector but we have a scalar or tuple,
            // box it into a singleton/flat Arrow vector (sequence unification).
            let (v, arg_kind) = if let Some(Kind::Vector(ek)) = expected_kind {
                if !matches!(arg_kind, Kind::Vector(_)) {
                    let ek = ek.as_ref().clone();
                    match &arg_kind {
                        Kind::Int | Kind::Bool => {
                            self.compile_scalar_as_singleton_vector(v, &arg_kind, &ek)?
                        }
                        Kind::Tuple(elems) => {
                            let elems = elems.clone();
                            self.compile_tuple_as_vector(v, &elems, &ek)?
                        }
                        _ => (v, arg_kind),
                    }
                } else {
                    (v, arg_kind)
                }
            } else {
                (v, arg_kind)
            };

            // When the callee expects (or doesn't expect) a TaggedUnion param —
            // e.g. a `+`-typed domain like `{0} + NatPos` — but the argument's
            // Kind disagrees, widen/narrow it. Mirrors `coerce_tagged_union_return`
            // at the call boundary instead of the return boundary; see
            // `coerce_call_arg` for why this needs the callee's recorded domain
            // set expression to disambiguate same-Kind `+` arms.
            let (v, arg_kind) = match expected_kind {
                Some(expected @ Kind::TaggedUnion(_))
                    if !matches!(arg_kind, Kind::TaggedUnion(_)) =>
                {
                    self.coerce_call_arg(v, arg_kind, expected, &lookup_key, arg_idx)?
                }
                Some(expected)
                    if matches!(arg_kind, Kind::TaggedUnion(_))
                        && !matches!(expected, Kind::TaggedUnion(_)) =>
                {
                    self.coerce_call_arg(v, arg_kind, expected, &lookup_key, arg_idx)?
                }
                _ => (v, arg_kind),
            };

            // int-soundness-plan phase 3 step 4b: tag/untag at the call
            // boundary when the argument's representation doesn't match
            // what the callee (or, for a dispatch call, the canonical
            // shared representation — see above) declares — e.g. an
            // ordinary tagged local passed into a `Kind::Int64` parameter,
            // or a Step-A-promoted call's raw result passed into an
            // ordinary tagged one.
            let (v, arg_kind) = match expected_kind {
                Some(Kind::Int64) if arg_kind == Kind::Int => (
                    self.ensure_raw_int64(v.into_int_value(), &arg_kind)?.into(),
                    Kind::Int64,
                ),
                Some(Kind::Int) if arg_kind == Kind::Int64 => (
                    self.ensure_tagged(v.into_int_value(), &arg_kind)?.into(),
                    Kind::Int,
                ),
                _ => (v, arg_kind),
            };

            // All function parameters are i64 (uniform ABI); widen any
            // narrower scalar (Bool i1, Signed32/Unsigned32/Char i32).
            let v_i64 = self.widen_scalar_to_i64(v, &arg_kind, "arg_ext")?;
            compiled_arg_values.push(v_i64);
        }
        let compiled_args: Vec<_> = compiled_arg_values.iter().map(|&v| v.into()).collect();
        let is_dispatch = matches!(target, CallTarget::Dispatch(_));

        let result_i64 = match target {
            CallTarget::Direct(name) => {
                let function = self.module.get_function(&name).ok_or_else(|| {
                    CompileError::UndefinedVariable {
                        name: callee.0.clone(),
                        span,
                    }
                })?;
                let call = self
                    .builder
                    .build_call(function, &compiled_args, "call")
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                call.try_as_basic_value()
                    .left()
                    .ok_or_else(|| CompileError::ice("void return in expression position"))?
            }
            CallTarget::Dispatch(candidates) => self.compile_overload_dispatch(
                &callee.0,
                &candidates,
                &compiled_arg_values,
                param_kinds_for_callee.as_deref().unwrap_or(&[]),
                span,
            )?,
        };

        // Restore the correct Kind after the call. For a `Dispatch` call,
        // `compile_overload_dispatch` already normalizes every candidate's
        // result to the canonical tagged `Int` before its `phi` merge (see
        // that function), so the call-site result here is `Int`, never
        // whichever candidate `lookup_key` happened to name.
        let raw_return_kind = self
            .fn_return_kinds
            .get(&lookup_key)
            .cloned()
            .unwrap_or(Kind::Int);
        let return_kind = if is_dispatch && raw_return_kind == Kind::Int64 {
            Kind::Int
        } else {
            raw_return_kind
        };
        match &return_kind {
            Kind::Bool => {
                let i1_val = self
                    .builder
                    .build_int_truncate(
                        result_i64.into_int_value(),
                        self.context.bool_type(),
                        "call_bool",
                    )
                    .map_err(|e| CompileError::ice(e.to_string()))?;
                Ok((i1_val.into(), Kind::Bool))
            }
            // Tuples and TaggedUnions are returned as struct values directly.
            // Union is i64 at this stage but we preserve the Kind for future stages.
            Kind::Tuple(_) | Kind::TaggedUnion(_) => Ok((result_i64, return_kind)),
            // Vector is an i64 pointer — pass through and preserve the Kind.
            Kind::Vector(_) | Kind::Set(_) => Ok((result_i64, return_kind)),
            // int-soundness-plan phase 3 step 4b: preserve the callee's real
            // declared Kind (`Int` vs raw `Int64`) instead of hardcoding
            // `Int` — a call into a Step-A-promoted or step-4a-split-Int64
            // function returns a raw word, and mislabelling it `Int` here
            // would make every downstream consumer treat it as tagged.
            _ => Ok((result_i64, return_kind)),
        }
    }
}
