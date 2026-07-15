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
    /// `'` was not followed by exactly one Unicode scalar value (accounting
    /// for escapes) before the closing `'` — `''`, `'ab'`, or an unterminated
    /// `'a`.
    InvalidCharLiteral {
        reason: String,
        span: Span,
    },
    /// A string literal (`"..."`) or char literal (`'...'`) ran off the end
    /// of the line/file before its closing quote.
    UnterminatedLiteral {
        quote: char,
        span: Span,
    },
    /// `\x` inside a char/string literal where `x` isn't one of the
    /// supported escapes (`n t r 0 \ ' " u`).
    InvalidEscape {
        found: String,
        span: Span,
    },
    /// `\u{...}` — malformed hex digits, missing braces, or a codepoint that
    /// isn't a valid Unicode scalar value (out of range, or a surrogate).
    InvalidUnicodeEscape {
        reason: String,
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
    /// A call to an overloaded name (backlog.md "function overloads —
    /// support different kinds") whose argument Kinds don't match any
    /// declared overload's parameter-Kind bucket — e.g. calling `f(true)`
    /// when only `f : Nat -> Nat` exists. Unlike an out-of-*domain* call
    /// (a solver-checked runtime obligation, since a value's domain
    /// membership isn't always statically decidable), an argument's Kind
    /// is always known at elaboration time, so this is caught here rather
    /// than deferred to the solver.
    NoMatchingOverload {
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
    /// A recursive named-set definition (design-decisions.md §3, "Recursive
    /// sets") has no way to bottom out — every union arm that could make it
    /// inhabited itself depends, directly or transitively, on the set being
    /// defined. Tier-1 structural recursion permanently rejects this shape
    /// (there is no runtime escape hatch, same as quotient-set idempotence);
    /// it is not a "not yet implemented" gap.
    IllFoundedRecursiveSet {
        name: String,
        span: Span,
    },
    /// The event-loop `main` contract (docs/design-decisions.md §6) is
    /// violated: a 2-arity `main` overload looks like it's attempting the
    /// `Char* * S -> Char* * S` shape but State isn't a named set, State
    /// differs between domain and range, or there's no matching `main : ->
    /// S` seed overload. A structural/shape check, not a proof obligation
    /// — there's nothing for cvc5 to prove here.
    EventLoopMainShape {
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
            Self::InvalidCharLiteral { reason, .. } => write!(f, "invalid char literal: {reason}"),
            Self::UnterminatedLiteral { quote, .. } => {
                write!(f, "unterminated literal, expected closing `{quote}`")
            }
            Self::InvalidEscape { found, .. } => write!(f, "unknown escape sequence `{found}`"),
            Self::InvalidUnicodeEscape { reason, .. } => {
                write!(f, "invalid unicode escape: {reason}")
            }
            Self::NamingConvention { message, .. } => write!(f, "naming: {message}"),
            Self::OverloadKindMismatch { name, detail, .. } => {
                write!(f, "overloads of `{name}` disagree: {detail}")
            }
            Self::NoMatchingOverload { name, detail, .. } => {
                write!(f, "no overload of `{name}` matches: {detail}")
            }
            Self::Unsupported { feature, .. } => write!(f, "not yet supported: {feature}"),
            Self::InvalidSetExpression { detail, .. } => {
                write!(f, "invalid set expression: {detail}")
            }
            Self::IllFoundedRecursiveSet { name, .. } => {
                write!(
                    f,
                    "cannot verify well-foundedness of recursive set `{name}` — \
                     every union arm depends on `{name}` itself with no base case"
                )
            }
            Self::EventLoopMainShape { detail, .. } => {
                write!(f, "event-loop `main`: {detail}")
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
            Self::InvalidCharLiteral { span, .. } => Some(*span),
            Self::UnterminatedLiteral { span, .. } => Some(*span),
            Self::InvalidEscape { span, .. } => Some(*span),
            Self::InvalidUnicodeEscape { span, .. } => Some(*span),
            Self::NamingConvention { span, .. } => Some(*span),
            Self::OverloadKindMismatch { span, .. } => Some(*span),
            Self::NoMatchingOverload { span, .. } => Some(*span),
            Self::Unsupported { span, .. } => Some(*span),
            Self::InvalidSetExpression { span, .. } => Some(*span),
            Self::IllFoundedRecursiveSet { span, .. } => Some(*span),
            Self::EventLoopMainShape { span, .. } => Some(*span),
            Self::Ice { .. } => None,
        }
    }
}
