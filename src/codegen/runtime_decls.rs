//! Declares every Cantor runtime function as an external symbol in the module.
//!
//! Split out of `mod.rs` as a pure refactor (no behaviour change) to keep
//! that file under the repo's line-count guideline.

use super::Compiler;

impl<'ctx> Compiler<'ctx> {
    /// Declare all Cantor runtime functions as external symbols in the module.
    ///
    /// Must be called before compiling any code that uses runtime sets.
    /// `into_jit_engine` (in `jit.rs`) registers the actual function pointers
    /// so the JIT can resolve the calls.
    pub fn declare_runtime_functions(&mut self) {
        let i64t = self.context.i64_type();
        let void = self.context.void_type();
        let ii   = &[i64t.into(), i64t.into()] as &[_]; // (set_ptr, val) -> ...
        let i    = &[i64t.into()] as &[_];               // (set_ptr) -> i64

        // Set(Int) ABI
        self.module.add_function("cantor_set_new_i64",      i64t.fn_type(&[], false),  None);
        self.module.add_function("cantor_set_insert_i64",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_contains_i64", i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_size_i64",     i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_set_get_i64",      i64t.fn_type(ii,   false), None);

        // Set(Bool) ABI — booleans passed as i64 (0/1) at the boundary
        self.module.add_function("cantor_set_new_bool",      i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_set_insert_bool",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_contains_bool", i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_set_size_bool",     i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_set_get_bool",      i64t.fn_type(ii,   false), None);

        // Vector(Int) ABI — Apache Arrow Int64Array, pointer-as-i64.
        self.module.add_function("cantor_vec_builder_new_i64",    i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_vec_builder_push_i64",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_builder_finish_i64", i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_len_i64",            i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_get_i64",            i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_push_i64",           i64t.fn_type(ii,   false), None);

        // Vector(Bool) ABI — Apache Arrow BooleanArray, pointer-as-i64.
        // Booleans passed as i64 (0/1) matching the uniform ABI.
        self.module.add_function("cantor_vec_builder_new_bool",    i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_vec_builder_push_bool",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_builder_finish_bool", i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_len_bool",            i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_vec_get_bool",            i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_push_bool",           i64t.fn_type(ii,   false), None);

        // Concatenation — both take two i64 pointers and return a new i64 pointer.
        self.module.add_function("cantor_vec_concat_i64",          i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_vec_concat_bool",         i64t.fn_type(ii,   false), None);

        // Nested vector (X** at any depth) — generic CantorListVec (Int64Array of opaque i64 ptrs).
        // All functions are suffix-free: the codegen never needs to know the Arrow child type.
        self.module.add_function("cantor_list_vec_builder_new",    i64t.fn_type(&[], false), None);
        self.module.add_function("cantor_list_vec_builder_push",   void.fn_type(ii,   false), None);
        self.module.add_function("cantor_list_vec_builder_finish", i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_list_vec_len",            i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_list_vec_get",            i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_list_vec_concat",         i64t.fn_type(ii,   false), None);

        // Struct vectors ((A * B)*) — backed by Arrow StructArray; all field values stored as i64.
        // push_field / get_field take (ptr, field_idx, value) — three i64 args.
        let iii = &[i64t.into(), i64t.into(), i64t.into()] as &[_];
        self.module.add_function("cantor_struct_vec_builder_new",        i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_struct_vec_builder_push_field", void.fn_type(iii,  false), None);
        self.module.add_function("cantor_struct_vec_builder_finish",     i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_struct_vec_len",                i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_struct_vec_get_field",          i64t.fn_type(iii,  false), None);
        self.module.add_function("cantor_struct_vec_concat",             i64t.fn_type(ii,   false), None);

        // Union vectors (Kind::Vector(Kind::TaggedUnion(arms))) — DenseUnionArray,
        // one StructArray child per arm (each with leaf_count(arm) Int64Array columns).
        // set_arm takes (builder, arm_idx, n_leaves) — three i64 args.
        // push_leaf takes (builder, arm_idx, leaf_idx, value) — four i64 args.
        // get_leaf takes (vec, row_idx, leaf_idx) — three i64 args.
        let iiii = &[i64t.into(), i64t.into(), i64t.into(), i64t.into()] as &[_];
        self.module.add_function("cantor_union_vec_builder_new",       i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_union_vec_builder_set_arm",   void.fn_type(iii,  false), None);
        self.module.add_function("cantor_union_vec_builder_push_leaf", void.fn_type(iiii, false), None);
        self.module.add_function("cantor_union_vec_builder_finish",    i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_union_vec_len",               i64t.fn_type(i,    false), None);
        self.module.add_function("cantor_union_vec_get_tag",           i64t.fn_type(ii,   false), None);
        self.module.add_function("cantor_union_vec_get_leaf",          i64t.fn_type(iii,  false), None);
        self.module.add_function("cantor_union_vec_concat",            i64t.fn_type(ii,   false), None);

        // int-soundness-plan phase 1: checked-arithmetic overflow abort.
        // Takes a pointer (as i64) to a null-terminated message; never returns
        // (the caller emits `unreachable` right after the call).
        self.module.add_function("cantor_overflow_abort", void.fn_type(i, false), None);
    }
}
