use crate::span::{Span, Symbol};

// ── Expressions ───────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    // Span-free constructors for tests and hand-built ASTs.
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

    pub fn if_then_else(cond: Expr, then_expr: Expr, else_expr: Expr) -> Self {
        Self::new(
            ExprKind::If {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            },
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
    If { cond: Box<Expr>, then_expr: Box<Expr>, else_expr: Box<Expr> },
    // Future: SetLit, Comprehension, Membership
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub, // also set difference at the semantic level; type checker disambiguates
    Mul, // also Cartesian product in signature position
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
    // Set operations (codegen stubs until sets are implemented)
    Union,     // |
    Intersect, // &
    SymDiff,   // ^
    // Logical (expect Bool operands)
    And,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

// ── Statements (imperative block bodies) ─────────────────────────────────────

#[derive(Debug, Clone)]
pub enum Stmt {
    /// `mut x = expr` — introduce a new mutable local.
    MutLet { name: Symbol, value: Expr, span: Span },
    /// `x = expr` — reassign an existing mutable (semantic analysis validates).
    Assign { name: Symbol, value: Expr, span: Span },
    /// `assert expr in S`
    Assert { expr: Expr, set: Expr, span: Span },
    /// `assume expr in S`
    Assume { expr: Expr, set: Expr, span: Span },
    /// Bare expression; the last `Expr` stmt in a block is the return value.
    Expr(Expr),
    /// Nested `{ stmts }` block — introduces a new scope.
    Block(Vec<Stmt>),
}

// ── Function definitions ──────────────────────────────────────────────────────

/// A named function parameter. Domain annotation added in phase 4 (cvc5).
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

/// One `name : Domain -> Range` line.
/// Domain is `None` for zero-argument functions (`name : -> Set`).
/// `*` in domain position means Cartesian product.
#[derive(Debug, Clone)]
pub struct FunctionSig {
    pub domain: Option<Expr>,
    pub range: Expr,
    pub span: Span,
}

/// The body of a function definition.
#[derive(Debug, Clone)]
pub enum FunctionBody {
    /// `= expr` — pure functional body.
    Expr(Expr),
    /// `{ stmts }` — imperative block body.
    Block(Vec<Stmt>),
}

/// A complete function definition: one or more signatures followed by a
/// single implementation. Multiple signatures = overloaded function (§7).
#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: Symbol,
    pub sigs: Vec<FunctionSig>,
    pub params: Vec<Param>,
    pub body: FunctionBody,
    pub span: Span,
}

// ── Top-level items ───────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum Item {
    FunctionDef(FunctionDef),
    // Future: SetDef, ModuleImport, …
}
