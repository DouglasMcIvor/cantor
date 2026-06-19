use crate::span::{Span, Symbol};

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    // Span-free constructors for use in tests and hand-built ASTs.
    pub fn int(n: i64) -> Self {
        Self::new(ExprKind::IntLit(n), Span::dummy())
    }

    pub fn bool(b: bool) -> Self {
        Self::new(ExprKind::BoolLit(b), Span::dummy())
    }

    pub fn var(name: &str) -> Self {
        Self::new(ExprKind::Var(Symbol::new(name)), Span::dummy())
    }

    pub fn binop(op: BinOp, lhs: Expr, rhs: Expr) -> Self {
        Self::new(
            ExprKind::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) },
            Span::dummy(),
        )
    }

    pub fn unop(op: UnOp, expr: Expr) -> Self {
        Self::new(ExprKind::UnOp { op, expr: Box::new(expr) }, Span::dummy())
    }

    pub fn call(callee: &str, args: Vec<Expr>) -> Self {
        Self::new(
            ExprKind::Call { callee: Symbol::new(callee), args },
            Span::dummy(),
        )
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    IntLit(i64),
    BoolLit(bool),
    Var(Symbol),
    BinOp { op: BinOp, lhs: Box<Expr>, rhs: Box<Expr> },
    UnOp { op: UnOp, expr: Box<Expr> },
    Call { callee: Symbol, args: Vec<Expr> },
    // Future: SetLit, Comprehension, Membership — stubs added when parser reaches them
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub, // also set difference at the semantic level; type checker disambiguates
    Mul,
    Div,
    // Comparison (produce Bool)
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Membership (produce Bool)
    In,
    NotIn,
    // Set operations (operands must be sets; codegen stubs until sets are implemented)
    Union,    // |
    Intersect, // &
    SymDiff,  // ^
    // Logical (expect Bool operands)
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

/// A named function parameter. Domain constraint added in phase 4 (cvc5).
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Symbol,
    pub span: Span,
}

impl Param {
    pub fn new(name: &str) -> Self {
        Self { name: Symbol::new(name), span: Span::dummy() }
    }
}
