//! Builtin `show` — converts a value of any currently-supported Kind into
//! its `Char*` (`Vector(Char)`) display form. Backs string interpolation
//! (`"a{expr}b"`, desugared to a `++`/`show(...)` chain in
//! `parser::expr`'s `desugar_interp_parts`) and is also directly callable
//! as an ordinary function.
//!
//! A Rust-level compiler intrinsic (recognized by name in
//! `expr_call::compile_call`, per-Kind `match` here), same recipe as
//! `from`/`char`/the auto-generated `distinct` constructors — not a
//! bundled-Cantor-source overload set, since its behaviour must recurse
//! through arbitrary compound Kinds at compile time.
//!
//! Display conventions (settled with the user, see the interpolation
//! design plan): a `Char*`/string always shows as its bare literal text,
//! at any nesting depth — `show(["ab","cd"])` prints `[ab, cd]`, not
//! `["ab", "cd"]`. Containers print in a literal-like shape: `(a, b)` for
//! `Tuple`, `[a, b]` for `Vector`, `{a, b}` for `Set`. A `distinct`/
//! quotient/named-Int-subset value erases to bare `Kind::Int` by codegen
//! time (`kind::set_kind`'s `DefKind::Distinct` arm) and so shows as its
//! raw underlying integer — a known, documented limitation, not a bug.
//!
//! `TaggedUnion` (`T | Fail | ...`) is not yet implemented here — see the
//! `Kind::TaggedUnion` arm below.

use inkwell::{
    IntPredicate,
    values::{AggregateValueEnum, BasicValueEnum},
};

use crate::{error::CompileError, kind::Kind, span::Span};

use super::Compiler;
use super::expr_vec::vector_len_fn_name;

/// Bundles `compile_show_loop`'s per-call-site parameters (basic-block name
/// prefix, which runtime size function to call, and the container's own
/// bracket text) to keep the method's argument count under clippy's limit —
/// same context-struct convention used elsewhere in `codegen` (see
/// `EncodeCtx`/`BlockCtx`/`LoopCtx` etc.).
struct ShowLoopSpec<'a> {
    block_prefix: &'a str,
    size_fn_name: &'a str,
    open: &'a str,
    close: &'a str,
    span: Span,
}

impl<'ctx> Compiler<'ctx> {
    /// Entry point, dispatched from `expr_call::compile_call`'s `"show"`
    /// arm. `span` is the call site's span, used only if this Kind (or one
    /// nested inside it) isn't supported yet.
    pub(super) fn compile_show(
        &self,
        kind: &Kind,
        val: BasicValueEnum<'ctx>,
        span: Span,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        match kind {
            Kind::Int | Kind::Int64 => {
                let tagged = self.ensure_tagged(val.into_int_value(), kind)?;
                self.call_show_bigint(tagged)
            }
            // Signed32/Unsigned32: sign-/zero-extend to i64 then tag, same
            // widening `from(x)` does (`expr_call.rs`), before formatting —
            // `cantor_show_bigint` only understands the tagged `Int` word
            // scheme.
            Kind::Signed32 => {
                let i64t = self.context.i64_type();
                let wide = self
                    .builder
                    .build_int_s_extend(val.into_int_value(), i64t, "show_s32")
                    .map_err(err)?;
                let tagged = self.ensure_tagged(wide, &Kind::Int64)?;
                self.call_show_bigint(tagged)
            }
            Kind::Unsigned32 => {
                let i64t = self.context.i64_type();
                let wide = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "show_u32")
                    .map_err(err)?;
                let tagged = self.ensure_tagged(wide, &Kind::Int64)?;
                self.call_show_bigint(tagged)
            }
            Kind::Bool => {
                let true_str = self.compile_char_star_literal("true")?;
                let false_str = self.compile_char_star_literal("false")?;
                self.builder
                    .build_select(val.into_int_value(), true_str, false_str, "show_bool")
                    .map_err(err)
            }
            Kind::Char => {
                let i64t = self.context.i64_type();
                let cp = self
                    .builder
                    .build_int_z_extend(val.into_int_value(), i64t, "show_char_cp")
                    .map_err(err)?;
                self.build_i64_vec(&[cp])
            }
            // Singletons — the value carries no information beyond its own
            // membership, so the display text is a compile-time constant.
            Kind::Fail => self.compile_char_star_literal("fail"),
            Kind::None => self.compile_char_star_literal("none"),
            // `Tuple([Fail|None, Int])` is the generic fallible-value wire
            // struct (`Compiler::fail_struct_type`) — used both for a
            // literal `fail`/`fail n`/`none` expression AND for any
            // ordinary `T | Fail`/`T | None`-typed value
            // (`kind::IfMerge::CoerceToFailStruct` erases the success arm's
            // real Kind down to this fixed marker). It is NOT always a
            // failure — reading the runtime tag is required, never assume.
            Kind::Tuple(elems) if crate::kind::is_propagation_tuple(elems) => {
                self.compile_show_fail_struct(val, span)
            }
            Kind::Tuple(elems) => self.compile_show_tuple(elems, val, span),
            // A string shows as its own bare text, at any nesting depth —
            // this is also what makes interpolating an existing `Char*`
            // variable a no-op rather than re-wrapping it in `[...]`.
            Kind::Vector(ek) if **ek == Kind::Char => Ok(val),
            Kind::Vector(ek) => self.compile_show_vector(ek, val, span),
            Kind::Set(ek) => self.compile_show_set(ek, val, span),
            Kind::TaggedUnion(_) => Err(CompileError::Unsupported {
                feature: "show on a union value (T | Fail | ...)".to_owned(),
                span,
            }),
        }
    }

    /// Calls the `cantor_show_bigint` runtime primitive — `word` must
    /// already be in the tagged `Int` representation (small-int-shifted or
    /// boxed, `runtime::bigint`'s scheme), never a raw `Int64` word.
    fn call_show_bigint(
        &self,
        word: inkwell::values::IntValue<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let fn_val = self
            .module
            .get_function("cantor_show_bigint")
            .ok_or_else(|| CompileError::ice("cantor_show_bigint not declared"))?;
        self.builder
            .build_call(fn_val, &[word.into()], "show_bigint")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_show_bigint returned void"))
    }

    /// Concatenates two `Char*` values via the `cantor_vec_concat_i64`
    /// runtime primitive (the same one `++`/`compile_vec_concat` use for
    /// `Char*` — `expr.rs`'s `compile_vec_concat`, `Kind::Char` reuses the
    /// plain `_i64` vector ABI verbatim).
    fn concat_char_star(
        &self,
        a: BasicValueEnum<'ctx>,
        b: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let fn_val = self
            .module
            .get_function("cantor_vec_concat_i64")
            .ok_or_else(|| CompileError::ice("cantor_vec_concat_i64 not declared"))?;
        self.builder
            .build_call(fn_val, &[a.into(), b.into()], "show_concat")
            .map_err(|e| CompileError::ice(e.to_string()))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_vec_concat_i64 returned void"))
    }

    /// Builds a `Char*` value from a fixed list of i64 codepoint words —
    /// each may be a compile-time constant (`compile_char_star_literal`'s
    /// fixed-text pieces: `"true"`, `"("`, `", "`, …) or a single
    /// runtime-computed one (`show`'s `Char` case). Emits the same
    /// builder-new/push-per-codepoint/finish sequence
    /// `event_loop::encode_char_star` runs at runtime, just as LLVM IR.
    fn build_i64_vec(
        &self,
        elems: &[inkwell::values::IntValue<'ctx>],
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let new_fn = self
            .module
            .get_function("cantor_vec_builder_new_i64")
            .ok_or_else(|| CompileError::ice("cantor_vec_builder_new_i64 not declared"))?;
        let push_fn = self
            .module
            .get_function("cantor_vec_builder_push_i64")
            .ok_or_else(|| CompileError::ice("cantor_vec_builder_push_i64 not declared"))?;
        let finish_fn = self
            .module
            .get_function("cantor_vec_builder_finish_i64")
            .ok_or_else(|| CompileError::ice("cantor_vec_builder_finish_i64 not declared"))?;

        let builder_ptr = self
            .builder
            .build_call(new_fn, &[], "show_lit_builder")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_vec_builder_new_i64 returned void"))?;
        for &elem in elems {
            self.builder
                .build_call(push_fn, &[builder_ptr.into(), elem.into()], "show_lit_push")
                .map_err(err)?;
        }
        self.builder
            .build_call(finish_fn, &[builder_ptr.into()], "show_lit")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice("cantor_vec_builder_finish_i64 returned void"))
    }

    /// Builds a compile-time-constant `Char*` value — every fixed-text
    /// piece `show` needs (`"true"`/`"false"`/`"fail"`/`"none"` and every
    /// punctuation piece: `", "`, `"["`, `"]"`, `"("`, `")"`, `"{"`, `"}"`).
    fn compile_char_star_literal(&self, s: &str) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let i64t = self.context.i64_type();
        let elems: Vec<_> = s
            .chars()
            .map(|c| i64t.const_int(c as u32 as u64, false))
            .collect();
        self.build_i64_vec(&elems)
    }

    /// A `Tuple([Fail|None, Int])` value — the generic fallible-value wire
    /// struct (`Compiler::fail_struct_type`: `{i8 tag, i64 payload}`,
    /// `TAG_SUCCESS`/`TAG_FAIL`/`TAG_NONE`). This exact Kind backs BOTH a
    /// literal `fail`/`fail n`/`none` expression AND any ordinary
    /// `T | Fail`/`T | None`-typed value — `kind::IfMerge::CoerceToFailStruct`
    /// always erases the real success-arm Kind down to this fixed `Int`
    /// marker (the same simplification `compile_try`'s payload extraction
    /// already relies on, `expr.rs`'s `compile_try`, not new here). So this
    /// must be a genuine runtime tag read + 3-way branch: assuming "this
    /// Kind ⇒ definitely a fail" (an earlier version of this function did)
    /// silently mis-displays every ordinary success value of a `T | Fail`
    /// variable as `"fail <bits>"` — caught via manual smoke testing, not
    /// a hypothetical. `none`'s payload is always 0 (no `NoneWith` exists,
    /// see `ast::ExprKind`), so the `None` arm never shows a payload.
    fn compile_show_fail_struct(
        &self,
        val: BasicValueEnum<'ctx>,
        span: Span,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let struct_val = val.into_struct_value();
        let tag = self
            .builder
            .build_extract_value(struct_val, 0, "show_fs_tag")
            .map_err(err)?
            .into_int_value();
        let payload = self
            .builder
            .build_extract_value(struct_val, 1, "show_fs_payload")
            .map_err(err)?;

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("show on a fallible value outside a function"))?;
        let fail_bb = self.context.append_basic_block(function, "show_fs_fail");
        let none_bb = self.context.append_basic_block(function, "show_fs_none");
        let success_bb = self.context.append_basic_block(function, "show_fs_success");
        let after_bb = self.context.append_basic_block(function, "show_fs_after");

        let i8t = self.context.i8_type();
        self.builder
            .build_switch(
                tag,
                success_bb,
                &[
                    (i8t.const_int(Self::TAG_FAIL, false), fail_bb),
                    (i8t.const_int(Self::TAG_NONE, false), none_bb),
                ],
            )
            .map_err(err)?;

        self.builder.position_at_end(fail_bb);
        let prefix = self.compile_char_star_literal("fail ")?;
        let payload_str = self.compile_show(&Kind::Int, payload, span)?;
        let fail_str = self.concat_char_star(prefix, payload_str)?;
        self.builder
            .build_unconditional_branch(after_bb)
            .map_err(err)?;
        let fail_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(none_bb);
        let none_str = self.compile_char_star_literal("none")?;
        self.builder
            .build_unconditional_branch(after_bb)
            .map_err(err)?;
        let none_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(success_bb);
        let success_str = self.compile_show(&Kind::Int, payload, span)?;
        self.builder
            .build_unconditional_branch(after_bb)
            .map_err(err)?;
        let success_bb_end = self.builder.get_insert_block().unwrap();

        self.builder.position_at_end(after_bb);
        let phi = self
            .builder
            .build_phi(self.context.i64_type(), "show_fs_result")
            .map_err(err)?;
        phi.add_incoming(&[
            (&fail_str, fail_bb_end),
            (&none_str, none_bb_end),
            (&success_str, success_bb_end),
        ]);
        Ok(phi.as_basic_value())
    }

    /// `Tuple(elems)` — a genuine multi-field tuple (not the fallible-value
    /// wire struct, see `compile_show_fail_struct`). Arity is known at
    /// compile time, so this unrolls into a fixed sequence of field
    /// extracts + recursive `show` calls + concatenation, no runtime loop
    /// needed.
    fn compile_show_tuple(
        &self,
        elems: &[Kind],
        val: BasicValueEnum<'ctx>,
        span: Span,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let sv = AggregateValueEnum::StructValue(val.into_struct_value());
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let mut acc = self.compile_char_star_literal("(")?;
        for (i, ek) in elems.iter().enumerate() {
            if i > 0 {
                let sep = self.compile_char_star_literal(", ")?;
                acc = self.concat_char_star(acc, sep)?;
            }
            let field = self
                .builder
                .build_extract_value(sv, i as u32, "show_tuple_field")
                .map_err(err)?;
            let field_str = self.compile_show(ek, field, span)?;
            acc = self.concat_char_star(acc, field_str)?;
        }
        let close = self.compile_char_star_literal(")")?;
        self.concat_char_star(acc, close)
    }

    /// `Vector(ek)`, `ek != Char` — length is only known at runtime, so
    /// this emits a genuine loop (the established 3-basic-block idiom,
    /// `loops.rs`'s `compile_for_in_runtime_vector`), accumulating into a
    /// `Char*` alloca rather than a raw LLVM `phi` (matching this
    /// codebase's established convention for loop-threaded values).
    fn compile_show_vector(
        &self,
        ek: &Kind,
        val: BasicValueEnum<'ctx>,
        span: Span,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let len_fn_name = vector_len_fn_name(ek)?;
        self.compile_show_loop(
            ShowLoopSpec {
                block_prefix: "show_vec",
                size_fn_name: len_fn_name,
                open: "[",
                close: "]",
                span,
            },
            val,
            |slf, i_val| slf.compile_vector_elem_get(val, ek, i_val.into()),
        )
    }

    /// `Set(ek)` — `ek` is always a scalar word Kind (`Kind::Set`'s own
    /// construction restricts it to `Int`/`Int64`/`Bool`/`Fail`/`None`, see
    /// `kind.rs`), so this terminates directly into `compile_show`'s scalar
    /// arms with no further recursion. Same loop shape as
    /// `compile_show_vector`, wrapped in `{`/`}` instead of `[`/`]`, using
    /// the set accessor functions (mirrors `loops.rs`'s
    /// `compile_for_in_runtime_set`, including its tagged-vs-raw `Set(Int)`
    /// distinction).
    fn compile_show_set(
        &self,
        ek: &Kind,
        val: BasicValueEnum<'ctx>,
        span: Span,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let int_is_tagged = *ek == Kind::Int && self.tagging_active();
        let (size_fn_name, get_fn_name) = match ek {
            Kind::Int if int_is_tagged => {
                ("cantor_tagged_set_size_i64", "cantor_tagged_set_get_i64")
            }
            Kind::Int | Kind::Int64 => ("cantor_set_size_i64", "cantor_set_get_i64"),
            Kind::Bool | Kind::Fail | Kind::None => ("cantor_set_size_bool", "cantor_set_get_bool"),
            other => {
                return Err(CompileError::ice(format!(
                    "show on Set({other:?}): not a legal runtime set element kind"
                )));
            }
        };
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        self.compile_show_loop(
            ShowLoopSpec {
                block_prefix: "show_set",
                size_fn_name,
                open: "{",
                close: "}",
                span,
            },
            val,
            |slf, i_val| {
                let get_fn = slf
                    .module
                    .get_function(get_fn_name)
                    .ok_or_else(|| CompileError::ice(format!("{get_fn_name} not declared")))?;
                let raw = slf
                    .builder
                    .build_call(get_fn, &[val.into(), i_val.into()], "show_set_elem_raw")
                    .map_err(err)?
                    .try_as_basic_value()
                    .left()
                    .ok_or_else(|| CompileError::ice(format!("{get_fn_name} returned void")))?;
                match ek {
                    Kind::Int if int_is_tagged => Ok((raw, Kind::Int)),
                    Kind::Int | Kind::Int64 => Ok((
                        slf.ensure_tagged(raw.into_int_value(), &Kind::Int64)?
                            .into(),
                        Kind::Int,
                    )),
                    Kind::Bool | Kind::Fail | Kind::None => {
                        let i1 = slf
                            .builder
                            .build_int_truncate(
                                raw.into_int_value(),
                                slf.context.bool_type(),
                                "show_set_elem_bool",
                            )
                            .map_err(err)?;
                        Ok((i1.into(), ek.clone()))
                    }
                    other => Err(CompileError::ice(format!(
                        "show on Set({other:?}): not a legal runtime set element kind"
                    ))),
                }
            },
        )
    }

    /// Shared 3-basic-block loop shape behind `compile_show_vector`/
    /// `compile_show_set`: `spec.size_fn_name(val)` gives the element count;
    /// `get_elem(i)` fetches/decodes element `i` as a `(value, Kind)` pair
    /// for each iteration; the result accumulates as `open elem, elem, …
    /// close` — `Vector` passes `"["`/`"]"`, `Set` passes `"{"`/`"}"`.
    fn compile_show_loop(
        &self,
        spec: ShowLoopSpec,
        val: BasicValueEnum<'ctx>,
        get_elem: impl Fn(
            &Self,
            inkwell::values::IntValue<'ctx>,
        ) -> Result<(BasicValueEnum<'ctx>, Kind), CompileError>,
    ) -> Result<BasicValueEnum<'ctx>, CompileError> {
        let ShowLoopSpec {
            block_prefix,
            size_fn_name,
            open,
            close,
            span,
        } = spec;
        let err = |e: inkwell::builder::BuilderError| CompileError::ice(e.to_string());
        let i64t = self.context.i64_type();

        let size_fn = self
            .module
            .get_function(size_fn_name)
            .ok_or_else(|| CompileError::ice(format!("{size_fn_name} not declared")))?;
        let n = self
            .builder
            .build_call(size_fn, &[val.into()], "show_loop_n")
            .map_err(err)?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::ice(format!("{size_fn_name} returned void")))?
            .into_int_value();

        let i_ptr = self
            .builder
            .build_alloca(i64t, "show_loop_i")
            .map_err(err)?;
        self.builder
            .build_store(i_ptr, i64t.const_int(0, false))
            .map_err(err)?;
        let open = self.compile_char_star_literal(open)?;
        let acc_ptr = self
            .builder
            .build_alloca(i64t, "show_loop_acc")
            .map_err(err)?;
        self.builder
            .build_store(acc_ptr, open.into_int_value())
            .map_err(err)?;

        let function = self
            .current_fn
            .ok_or_else(|| CompileError::ice("show on a Vector/Set outside a function"))?;
        let cond_bb = self
            .context
            .append_basic_block(function, &format!("{block_prefix}_cond"));
        let body_bb = self
            .context
            .append_basic_block(function, &format!("{block_prefix}_body"));
        let after_bb = self
            .context
            .append_basic_block(function, &format!("{block_prefix}_after"));

        self.builder
            .build_unconditional_branch(cond_bb)
            .map_err(err)?;

        self.builder.position_at_end(cond_bb);
        let i_val = self
            .builder
            .build_load(i64t, i_ptr, "show_loop_i_val")
            .map_err(err)?
            .into_int_value();
        let cond = self
            .builder
            .build_int_compare(IntPredicate::SLT, i_val, n, "show_loop_cond")
            .map_err(err)?;
        self.builder
            .build_conditional_branch(cond, body_bb, after_bb)
            .map_err(err)?;

        // Body: append `", "` before every element but the first, then the
        // element's own `show`. The separator is always computed (even on
        // the first iteration, where it's discarded via `select`) rather
        // than genuinely branched around — unlike `TaggedUnion` tag
        // dispatch, concatenating two valid `Char*` values is always safe,
        // just occasionally wasted work, so a real branch (two more blocks,
        // another merge point) isn't worth the complexity here.
        self.builder.position_at_end(body_bb);
        let acc_val = self
            .builder
            .build_load(i64t, acc_ptr, "show_loop_acc_val")
            .map_err(err)?;
        let (elem_val, elem_k) = get_elem(self, i_val)?;
        let elem_str = self.compile_show(&elem_k, elem_val, span)?;
        let is_first = self
            .builder
            .build_int_compare(
                IntPredicate::EQ,
                i_val,
                i64t.const_int(0, false),
                "show_loop_is_first",
            )
            .map_err(err)?;
        let sep = self.compile_char_star_literal(", ")?;
        let acc_with_sep = self.concat_char_star(acc_val, sep)?;
        let acc_before_elem = self
            .builder
            .build_select(is_first, acc_val, acc_with_sep, "show_loop_acc_sep")
            .map_err(err)?;
        let acc_next = self.concat_char_star(acc_before_elem, elem_str)?;
        self.builder
            .build_store(acc_ptr, acc_next.into_int_value())
            .map_err(err)?;
        let i_curr = self
            .builder
            .build_load(i64t, i_ptr, "show_loop_i_curr")
            .map_err(err)?
            .into_int_value();
        let i_next = self
            .builder
            .build_int_add(i_curr, i64t.const_int(1, false), "show_loop_i_next")
            .map_err(err)?;
        self.builder.build_store(i_ptr, i_next).map_err(err)?;
        self.builder
            .build_unconditional_branch(cond_bb)
            .map_err(err)?;

        self.builder.position_at_end(after_bb);
        let acc_final = self
            .builder
            .build_load(i64t, acc_ptr, "show_loop_acc_final")
            .map_err(err)?;
        let close = self.compile_char_star_literal(close)?;
        self.concat_char_star(acc_final, close)
    }
}
