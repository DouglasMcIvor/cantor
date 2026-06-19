use std::fmt;

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

    pub fn set_lit(elements: Vec<Expr>) -> Self {
        Self::new(ExprKind::SetLit(elements), Span::dummy())
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
    /// `{ expr, expr, … }` — explicit set literal; used in signature position.
    SetLit(Vec<Expr>),
    // Future: Comprehension
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

// ── Display ───────────────────────────────────────────────────────────────────

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IntLit(n) => write!(f, "{n}"),
            Self::BoolLit(b) => write!(f, "{b}"),
            Self::Var(sym) => write!(f, "{sym}"),
            Self::UnOp { op, expr } => match op {
                UnOp::Neg => write!(f, "-{expr}"),
                UnOp::Not => write!(f, "not {expr}"),
            },
            Self::BinOp { op, lhs, rhs } => {
                // Parenthesise sub-expressions that have lower precedence than `op`.
                let lhs_str = if needs_parens_left(op, &lhs.kind) {
                    format!("({lhs})")
                } else {
                    format!("{lhs}")
                };
                let rhs_str = if needs_parens_right(op, &rhs.kind) {
                    format!("({rhs})")
                } else {
                    format!("{rhs}")
                };
                write!(f, "{lhs_str} {op} {rhs_str}")
            }
            Self::Call { callee, args } => {
                write!(f, "{callee}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            Self::If { cond, then_expr, else_expr } => {
                write!(f, "if {cond} then {then_expr} else {else_expr}")
            }
            Self::SetLit(elements) => {
                write!(f, "{{")?;
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{e}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// Returns true when `child` (on the left of `parent_op`) needs parentheses.
fn needs_parens_left(parent: &BinOp, child: &ExprKind) -> bool {
    let ExprKind::BinOp { op: child_op, .. } = child else { return false };
    binop_prec(child_op) < binop_prec(parent)
}

/// Returns true when `child` (on the right of `parent_op`) needs parentheses.
fn needs_parens_right(parent: &BinOp, child: &ExprKind) -> bool {
    let ExprKind::BinOp { op: child_op, .. } = child else { return false };
    // Right side also needs parens when equal precedence and left-associative
    // (all our binary operators are left-associative).
    binop_prec(child_op) <= binop_prec(parent)
}

/// Precedence tier — higher number binds tighter.
fn binop_prec(op: &BinOp) -> u8 {
    match op {
        BinOp::Or                               => 1,
        BinOp::And                              => 2,
        BinOp::Eq | BinOp::Ne | BinOp::Lt
        | BinOp::Le | BinOp::Gt | BinOp::Ge
        | BinOp::In | BinOp::NotIn             => 3,
        BinOp::Union                            => 4,
        BinOp::SymDiff                          => 5,
        BinOp::Intersect                        => 6,
        BinOp::Add | BinOp::Sub                 => 7,
        BinOp::Mul | BinOp::Div                 => 8,
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Add       => "+",
            Self::Sub       => "-",
            Self::Mul       => "*",
            Self::Div       => "/",
            Self::Eq        => "==",
            Self::Ne        => "!=",
            Self::Lt        => "<",
            Self::Le        => "<=",
            Self::Gt        => ">",
            Self::Ge        => ">=",
            Self::In        => "in",
            Self::NotIn     => "not in",
            Self::Union     => "|",
            Self::Intersect => "&",
            Self::SymDiff   => "^",
            Self::And       => "and",
            Self::Or        => "or",
        })
    }
}

impl fmt::Display for FunctionSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.domain {
            None    => write!(f, "-> {}", self.range),
            Some(d) => write!(f, "{d} -> {}", self.range),
        }
    }
}
