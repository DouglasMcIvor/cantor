use crate::span::{offset_to_line_col, Span};

#[derive(Debug, Clone)]
pub enum CompileError {
    UndefinedVariable { name: String, span: Span },
    TypeMismatch { expected: &'static str, found: &'static str, span: Span },
    UnexpectedToken { expected: String, found: String, span: Span },
    InvalidIntLiteral { text: String, span: Span },
    NamingConvention { message: String, span: Span },
    // Future: DomainViolation, RangeViolation (driven by cvc5 unsat core)
    Internal(String),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedVariable { name, .. } => write!(f, "undefined variable `{name}`"),
            Self::TypeMismatch { expected, found, .. } => {
                write!(f, "type mismatch: expected {expected}, found {found}")
            }
            Self::UnexpectedToken { expected, found, .. } => {
                write!(f, "expected {expected}, found {found}")
            }
            Self::InvalidIntLiteral { text, .. } => {
                write!(f, "invalid integer literal `{text}`")
            }
            Self::NamingConvention { message, .. } => write!(f, "naming: {message}"),
            Self::Internal(msg) => write!(f, "internal compiler error: {msg}"),
        }
    }
}

impl std::error::Error for CompileError {}

impl CompileError {
    /// Return the 1-based (line, column) of this error's span within `src`,
    /// or `None` for internal errors that carry no source location.
    pub fn location(&self, src: &str) -> Option<(u32, u32)> {
        let span = self.span()?;
        Some(offset_to_line_col(src, span.start))
    }

    fn span(&self) -> Option<Span> {
        match self {
            Self::UndefinedVariable  { span, .. } => Some(*span),
            Self::TypeMismatch       { span, .. } => Some(*span),
            Self::UnexpectedToken    { span, .. } => Some(*span),
            Self::InvalidIntLiteral  { span, .. } => Some(*span),
            Self::NamingConvention   { span, .. } => Some(*span),
            Self::Internal(_)                     => None,
        }
    }
}
