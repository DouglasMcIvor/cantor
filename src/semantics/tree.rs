//! The `SemanticTree` — an elaborated mirror of `ast::{Expr, Stmt, Item}` with
//! two differences from the raw AST:
//!
//! 1. Every node carries its resolved `Kind` (`SemExpr::kind_of`), computed once
//!    by `elaborate` instead of being re-derived on demand by callers.
//! 2. `BinOp::Add/Sub/Mul/Div` — the four operators whose meaning depends on
//!    whether they appear in value position (arithmetic) or set position
//!    (disjoint union / set difference / Cartesian product / set quotient) —
//!    are resolved into distinct `SemExprKind` variants. After elaboration
//!    there is no shared "could mean either" node left for a consumer to
//!    misinterpret; `elaborate` is the one place that decision gets made,
//!    using the position each sub-expression was actually found in.
//!
//! All other binary operators (comparisons, `in`/`not in`, `|`/`&`/`^`, `++`,
//! `and`/`or`) have exactly one meaning regardless of position, so they keep
//! using `ast::BinOp`/`ast::UnOp` directly rather than inventing parallel enums.

use crate::ast::{BinOp, Param, UnOp};
use crate::kind::Kind;
use crate::span::{Span, Symbol};

#[derive(Debug, Clone)]
pub struct SemExpr {
    pub kind: SemExprKind,
    pub kind_of: Kind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum SemExprKind {
    IntLit(i64),
    BoolLit(bool),
    Var(Symbol),

    /// Value-position `+`.
    Add(Box<SemExpr>, Box<SemExpr>),
    /// Set-position `+` — disjoint union; arms are tagged at runtime and are
    /// never deduplicated by Kind, even when they share one (mirrors `distinct`).
    DisjointUnion(Box<SemExpr>, Box<SemExpr>),
    /// Value-position `-`.
    Sub(Box<SemExpr>, Box<SemExpr>),
    /// Set-position `-` — set difference.
    SetDifference(Box<SemExpr>, Box<SemExpr>),
    /// Value-position `*`.
    Mul(Box<SemExpr>, Box<SemExpr>),
    /// Set-position `*` — Cartesian product.
    CartesianProduct(Box<SemExpr>, Box<SemExpr>),
    /// Value-position `/`.
    Div(Box<SemExpr>, Box<SemExpr>),
    /// Set-position `/` — set quotient. No consumer implements this yet;
    /// it exists so that misuse fails loudly instead of silently aliasing
    /// the LHS's Kind the way the pre-elaboration code path did.
    SetQuotient(Box<SemExpr>, Box<SemExpr>),

    /// Every other binary operator — single meaning regardless of position.
    BinOp { op: BinOp, lhs: Box<SemExpr>, rhs: Box<SemExpr> },
    UnOp { op: UnOp, expr: Box<SemExpr> },

    Call { callee: Symbol, args: Vec<SemExpr> },
    If { cond: Box<SemExpr>, then_expr: Box<SemExpr>, else_expr: Box<SemExpr> },
    /// `{ expr, … }` — explicit set literal.
    SetLit(Vec<SemExpr>),
    /// `expr?`
    Try(Box<SemExpr>),
    FailLit,
    FailWith(Box<SemExpr>),
    Comprehension {
        output: Box<SemExpr>,
        var: Symbol,
        source: Box<SemExpr>,
        filter: Option<Box<SemExpr>>,
    },
    Tuple(Vec<SemExpr>),
    Proj { base: Box<SemExpr>, index: usize },
    Index { base: Box<SemExpr>, index: Box<SemExpr> },
    /// `X*` — always set position; describes the set of finite sequences of `X`.
    KleeneStar(Box<SemExpr>),
}

// ── Statements ────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct SemDestructBinding {
    pub name: Symbol,
    pub constraint: Option<SemExpr>,
}

#[derive(Debug, Clone)]
pub enum SemAssertElse {
    FailWith(SemExpr),
    Return(SemExpr),
}

#[derive(Debug, Clone)]
pub enum SemStmt {
    Let { name: Symbol, constraint: SemExpr, value: SemExpr, span: Span },
    MutLet { name: Symbol, constraint: SemExpr, value: SemExpr, span: Span },
    Assign { name: Symbol, value: SemExpr, span: Span },
    DestructLet { bindings: Vec<SemDestructBinding>, tuple_constraint: Option<SemExpr>, value: SemExpr, span: Span },
    DestructMutLet { bindings: Vec<SemDestructBinding>, tuple_constraint: Option<SemExpr>, value: SemExpr, span: Span },
    DestructAssign { names: Vec<Symbol>, value: SemExpr, span: Span },
    Require { predicate: SemExpr, span: Span },
    Assert { predicate: SemExpr, else_clause: Option<SemAssertElse>, span: Span },
    Assume { predicate: SemExpr, span: Span },
    Expr(SemExpr),
    Block(Vec<SemStmt>),
    While { cond: SemExpr, body: Vec<SemStmt>, span: Span },
    ForIn { var: Symbol, set: SemExpr, body: Vec<SemStmt>, span: Span },
    Return { value: SemExpr, span: Span },
}

// ── Function and name definitions ───────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct SemFunctionSig {
    pub domain: Option<SemExpr>,
    pub range: SemExpr,
    /// Per-parameter Kind, decomposed from `domain` via `ast::param_set_exprs`.
    pub param_kinds: Vec<Kind>,
    pub return_kind: Kind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum SemFunctionBody {
    Expr(SemExpr),
    Block(Vec<SemStmt>),
}

#[derive(Debug, Clone)]
pub struct SemFunctionDef {
    pub name: Symbol,
    pub sigs: Vec<SemFunctionSig>,
    pub params: Vec<Param>,
    pub body: SemFunctionBody,
    /// Param/return Kind used to compile and check the body — taken from the
    /// first signature, mirroring `codegen::Compiler`'s existing rule that
    /// overloaded signatures must agree on the Kind of each position.
    pub param_kinds: Vec<Kind>,
    pub return_kind: Kind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct SemNameDef {
    pub name: Symbol,
    pub kind: crate::ast::DefKind,
    pub ty: Option<SemExpr>,
    pub value: SemExpr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum SemItem {
    FunctionDef(SemFunctionDef),
    NameDef(SemNameDef),
}

// ── AST utilities, mirrored for the elaborated tree ─────────────────────────

/// Flatten a left-associative `A * B * C` (`CartesianProduct`) into `[A, B, C]`.
/// Mirrors `ast::flatten_domain`, operating on the already-disambiguated variant.
pub fn flatten_cartesian_product(expr: &SemExpr) -> Vec<&SemExpr> {
    match &expr.kind {
        SemExprKind::CartesianProduct(lhs, rhs) => {
            let mut parts = flatten_cartesian_product(lhs);
            parts.push(rhs);
            parts
        }
        _ => vec![expr],
    }
}

/// Flatten a left-associative `(A + B) + C` (`DisjointUnion`) into `[A, B, C]`.
/// Mirrors `ast::flatten_disjoint_union`, operating on the already-disambiguated variant.
pub fn flatten_disjoint_union(expr: &SemExpr) -> Vec<&SemExpr> {
    match &expr.kind {
        SemExprKind::DisjointUnion(lhs, rhs) => {
            let mut arms = flatten_disjoint_union(lhs);
            arms.extend(flatten_disjoint_union(rhs));
            arms
        }
        _ => vec![expr],
    }
}
