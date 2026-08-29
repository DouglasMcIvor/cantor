//! `Float32` runtime support — `show`/CLI display only. Arithmetic and
//! comparisons need no runtime support at all (they compile straight to
//! LLVM `fadd`/`fcmp`/etc., unlike `Rational`, which is a boxed
//! `BigRational` and needs `cantor_rational_*` for everything). See
//! docs/design-decisions.md's `Float32`/`FiniteFloat32` section.

/// The display rendering shared by `show` and CLI output — mirrors
/// `ast::ExprKind::FloatLit`'s `Display` impl exactly (`infinity32`/
/// `nan32`/`-infinity32` for the special values, `{x}f` otherwise), so
/// runtime output and the compiler's own error/debug rendering never
/// diverge.
pub fn format_float32(x: f32) -> String {
    if x.is_nan() {
        "nan32".to_string()
    } else if x.is_infinite() {
        if x.is_sign_positive() {
            "infinity32".to_string()
        } else {
            "-infinity32".to_string()
        }
    } else {
        format!("{x}f")
    }
}

/// `show(x)` — renders as a `Char*` (`Vector(Char)`) value, same packaging
/// as `cantor_show_rational`. `word` is the ABI-widened i64 leaf (bitcast
/// f32 -> i32, zero-extended — see `codegen::Compiler::widen_scalar_to_i64`);
/// only the low 32 bits are meaningful.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_show_float32(word: i64) -> i64 {
    crate::event_loop::encode_char_star(&format_float32(f32::from_bits(word as u32)))
}

/// Renders as a heap-allocated null-terminated C string, for the CLI's
/// top-level result display — mirrors `cantor_rational_to_string`.
#[unsafe(no_mangle)]
pub extern "C" fn cantor_float32_to_string(word: i64) -> i64 {
    let s = format_float32(f32::from_bits(word as u32));
    let c_string = std::ffi::CString::new(s).expect("float32 display string has no interior NUL");
    c_string.into_raw() as i64
}
