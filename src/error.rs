use std::panic::Location;

use crate::span::{offset_to_line_col, Span};

/// Two categories today, with a third planned, kept deliberately separate
/// because each means something different to the person reading it and
/// will eventually render differently:
///
/// - Diagnostic-shaped variants (`UndefinedVariable`, `UnexpectedToken`,
///   ...): the user's program is invalid. Always has a Cantor source span.
/// - `Ice`: a compiler invariant was violated. Points at the *Rust* source
///   (via `Location::caller()`), not the user's file — the user's span is
///   irrelevant to debugging a compiler bug.
/// - PLANNED, not yet split out: `Unsupported`, for valid Cantor the
///   compiler doesn't implement yet (per the "unimplemented paths must
///   fail loudly" rule in CLAUDE.md — neither a user mistake nor a bug).
///   Most `Ice` sites today are genuine invariant violations (LLVM builder
///   failures, missing runtime declarations), but a few are really
///   user-reachable errors or "not implemented yet" gaps that haven't been
///   triaged out of `Ice` yet — that's ongoing follow-up work, not a
///   promise that every `Ice` today is a real compiler bug.
///
/// This is a different axis from the Class 1/2/3 taxonomy in
/// docs/design-decisions.md §4 — that's about Cantor's own runtime
/// semantics (`Fail`, `raises`); this enum is about the Rust compiler's
/// compile-time diagnostics.
#[derive(Debug, Clone)]
pub enum CompileError {
    UndefinedVariable { name: String, span: Span },
    UnexpectedToken { expected: String, found: String, span: Span },
    InvalidIntLiteral { text: String, span: Span },
    NamingConvention { message: String, span: Span },
    // Future: DomainViolation, RangeViolation (driven by cvc5 unsat core)

    /// A compiler invariant was violated — a bug in Cantor's compiler
    /// itself, not something the developer can fix by editing their
    /// program. `rust_location` is captured automatically by `ice()`.
    Ice { detail: String, rust_location: &'static Location<'static> },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedVariable { name, .. } => write!(f, "undefined variable `{name}`"),
            Self::UnexpectedToken { expected, found, .. } => {
                write!(f, "expected {expected}, found {found}")
            }
            Self::InvalidIntLiteral { text, .. } => {
                write!(f, "invalid integer literal `{text}`")
            }
            Self::NamingConvention { message, .. } => write!(f, "naming: {message}"),
            Self::Ice { detail, rust_location } => {
                write!(f, "internal compiler error ({rust_location}): {detail}")
            }
        }
    }
}

impl std::error::Error for CompileError {}

impl CompileError {
    /// Construct an `Ice`, capturing the caller's Rust source location
    /// automatically. Accepts anything `Display`, so existing call sites
    /// that used to do `Internal(e.to_string())` can just pass `e` directly.
    #[track_caller]
    pub fn ice(detail: impl std::fmt::Display) -> Self {
        Self::Ice { detail: detail.to_string(), rust_location: Location::caller() }
    }

    /// Return the 1-based (line, column) of this error's span within `src`,
    /// or `None` for ICEs, which carry a Rust location instead of a Cantor
    /// source span.
    pub fn location(&self, src: &str) -> Option<(u32, u32)> {
        let span = self.span()?;
        Some(offset_to_line_col(src, span.start))
    }

    fn span(&self) -> Option<Span> {
        match self {
            Self::UndefinedVariable  { span, .. } => Some(*span),
            Self::UnexpectedToken    { span, .. } => Some(*span),
            Self::InvalidIntLiteral  { span, .. } => Some(*span),
            Self::NamingConvention   { span, .. } => Some(*span),
            Self::Ice { .. }                      => None,
        }
    }
}
