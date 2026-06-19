use crate::span::Span;

#[derive(Debug, Clone)]
pub enum CompileError {
    UndefinedVariable { name: String, span: Span },
    TypeMismatch { expected: &'static str, found: &'static str, span: Span },
    UnexpectedToken { expected: String, found: String, span: Span },
    InvalidIntLiteral { text: String, span: Span },
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
            Self::Internal(msg) => write!(f, "internal compiler error: {msg}"),
        }
    }
}

impl std::error::Error for CompileError {}
