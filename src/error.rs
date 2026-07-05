use std::panic::Location;

use crate::span::{Span, offset_to_line_col};

/// Three categories, kept deliberately separate because each means
/// something different to the person reading it and will eventually
/// render differently:
///
/// - Diagnostic-shaped variants (`UndefinedVariable`, `UnexpectedToken`,
///   `UndefinedFunction`, ...): the user's program is invalid. Always has
///   a Cantor source span.
/// - `Unsupported`: valid Cantor the compiler doesn't implement yet, per
///   the "unimplemented paths must fail loudly" rule in CLAUDE.md. Neither
///   a user mistake nor a compiler bug — also has a Cantor source span.
/// - `Ice`: a compiler invariant was violated. Points at the *Rust* source
///   (via `Location::caller()`), not the user's file — the user's span is
///   irrelevant to debugging a compiler bug.
///
/// Most `Ice` sites today are genuine invariant violations (LLVM builder
/// failures, missing runtime declarations), but plenty are still
/// untriaged leftovers from before this split existed — some are really
/// user-reachable errors or "not implemented yet" gaps that haven't been
/// pulled out into `Diagnostic`/`Unsupported` yet. Per CLAUDE.md's
/// clean-as-you-go policy: when you're touching code near an `Ice` site
/// and can tell it's actually reachable by a user or a known gap, pull it
/// out into the right variant rather than leaving it; there's no plan to
/// bulk-migrate the rest until the richer-diagnostics work begins.
///
/// This is a different axis from the Class 1/2/3 taxonomy in
/// docs/design-decisions.md §4 — that's about Cantor's own runtime
/// semantics (`Fail`, `raises`); this enum is about the Rust compiler's
/// compile-time diagnostics.
#[derive(Debug, Clone)]
pub enum CompileError {
    UndefinedVariable {
        name: String,
        span: Span,
    },
    UndefinedFunction {
        name: String,
        span: Span,
    },
    UnexpectedToken {
        expected: String,
        found: String,
        span: Span,
    },
    InvalidIntLiteral {
        text: String,
        span: Span,
    },
    NamingConvention {
        message: String,
        span: Span,
    },
    /// Two `FunctionDef`s share a name and arity (an overload set, per
    /// int-soundness-plan phase 2 / design-decisions.md §7) but disagree on
    /// the Kind of a parameter or return position. `span` points at the
    /// later-declared overload that broke agreement.
    OverloadKindMismatch {
        name: String,
        detail: String,
        span: Span,
    },
    /// Valid Cantor the compiler doesn't implement yet.
    Unsupported {
        feature: String,
        span: Span,
    },
    /// A tuple/array literal (`(a, b, c)` or `[a, b, c]`) was used where a set
    /// expression was expected (a function's domain/range, a `let`
    /// constraint, …). Tuple/array literal syntax is value-position only —
    /// set-expression products are written with `*` (e.g. `Int * Int`).
    InvalidSetExpression {
        detail: String,
        span: Span,
    },
    // Future: DomainViolation, RangeViolation (driven by cvc5 unsat core)
    /// A compiler invariant was violated — a bug in Cantor's compiler
    /// itself, not something the developer can fix by editing their
    /// program. `rust_location` is captured automatically by `ice()`.
    Ice {
        detail: String,
        rust_location: &'static Location<'static>,
    },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedVariable { name, .. } => write!(f, "undefined variable `{name}`"),
            Self::UndefinedFunction { name, .. } => write!(f, "undefined function `{name}`"),
            Self::UnexpectedToken {
                expected, found, ..
            } => {
                write!(f, "expected {expected}, found {found}")
            }
            Self::InvalidIntLiteral { text, .. } => {
                write!(f, "invalid integer literal `{text}`")
            }
            Self::NamingConvention { message, .. } => write!(f, "naming: {message}"),
            Self::OverloadKindMismatch { name, detail, .. } => {
                write!(f, "overloads of `{name}` disagree: {detail}")
            }
            Self::Unsupported { feature, .. } => write!(f, "not yet supported: {feature}"),
            Self::InvalidSetExpression { detail, .. } => {
                write!(f, "invalid set expression: {detail}")
            }
            Self::Ice {
                detail,
                rust_location,
            } => {
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
        Self::Ice {
            detail: detail.to_string(),
            rust_location: Location::caller(),
        }
    }

    /// Whether this is a compiler bug rather than something the developer
    /// can fix by editing their program — the rendering layer uses this to
    /// decide whether to point at the user's source or add a "please
    /// report this" hint instead.
    pub fn is_ice(&self) -> bool {
        matches!(self, Self::Ice { .. })
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
            Self::UndefinedVariable { span, .. } => Some(*span),
            Self::UndefinedFunction { span, .. } => Some(*span),
            Self::UnexpectedToken { span, .. } => Some(*span),
            Self::InvalidIntLiteral { span, .. } => Some(*span),
            Self::NamingConvention { span, .. } => Some(*span),
            Self::OverloadKindMismatch { span, .. } => Some(*span),
            Self::Unsupported { span, .. } => Some(*span),
            Self::InvalidSetExpression { span, .. } => Some(*span),
            Self::Ice { .. } => None,
        }
    }
}
