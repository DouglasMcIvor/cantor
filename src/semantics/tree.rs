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
    BinOp {
        op: BinOp,
        lhs: Box<SemExpr>,
        rhs: Box<SemExpr>,
    },
    UnOp {
        op: UnOp,
        expr: Box<SemExpr>,
    },

    Call {
        callee: Symbol,
        args: Vec<SemExpr>,
    },
    If {
        cond: Box<SemExpr>,
        then_expr: Box<SemExpr>,
        else_expr: Box<SemExpr>,
    },
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
    Proj {
        base: Box<SemExpr>,
        index: usize,
    },
    Index {
        base: Box<SemExpr>,
        index: Box<SemExpr>,
    },
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
    Let {
        name: Symbol,
        constraint: SemExpr,
        value: SemExpr,
        span: Span,
    },
    MutLet {
        name: Symbol,
        constraint: SemExpr,
        value: SemExpr,
        span: Span,
    },
    Assign {
        name: Symbol,
        value: SemExpr,
        span: Span,
    },
    DestructLet {
        bindings: Vec<SemDestructBinding>,
        tuple_constraint: Option<SemExpr>,
        value: SemExpr,
        span: Span,
    },
    DestructMutLet {
        bindings: Vec<SemDestructBinding>,
        tuple_constraint: Option<SemExpr>,
        value: SemExpr,
        span: Span,
    },
    DestructAssign {
        names: Vec<Symbol>,
        value: SemExpr,
        span: Span,
    },
    Require {
        predicate: SemExpr,
        span: Span,
    },
    Assert {
        predicate: SemExpr,
        else_clause: Option<SemAssertElse>,
        span: Span,
    },
    Assume {
        predicate: SemExpr,
        span: Span,
    },
    Expr(SemExpr),
    Block(Vec<SemStmt>),
    While {
        cond: SemExpr,
        body: Vec<SemStmt>,
        span: Span,
    },
    ForIn {
        var: Symbol,
        set: SemExpr,
        body: Vec<SemStmt>,
        span: Span,
    },
    Return {
        value: SemExpr,
        span: Span,
    },
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
    /// int-soundness-plan phase 3: true only for the `Int64`/`BigInt`
    /// overload pair the compiler will synthesize from a single unbounded-
    /// `Int` signature — never set for anything elaborated from user source
    /// (`elaborate_function_def` always sets this to `false`). Nothing
    /// produces `true` here yet; step 4 (codegen) is what will generate
    /// such a pair. `check_overload_kind_agreement` is the only place this
    /// is read: a Kind mismatch between two members of the same (name,
    /// arity) group is allowed *only* when both are marked, keeping the
    /// exception narrow and structural rather than a general relaxation —
    /// see design-decisions.md §7 and int-soundness-plan.md's "Phase 3"
    /// section for why this stays scoped to the compiler's own split.
    pub compiler_generated_split: bool,
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

/// Flatten a left-associative `A | B | C` or `A + B + C` into `[A, B, C]`.
/// Mirrors `solver::sort::flatten_any_union`, treating `|` (`BinOp::Union`,
/// unaffected variant) and `+` (`DisjointUnion`, disambiguated variant) the
/// same way — both need one arm per constructor in a cross-kind union
/// datatype, regardless of the `|`-collapses-same-kind vs.
/// `+`-always-tags distinction that matters for `Kind` computation.
pub fn flatten_any_union(expr: &SemExpr) -> Vec<&SemExpr> {
    match &expr.kind {
        SemExprKind::BinOp {
            op: BinOp::Union,
            lhs,
            rhs,
        } => {
            let mut arms = flatten_any_union(lhs);
            arms.push(rhs);
            arms
        }
        SemExprKind::DisjointUnion(lhs, rhs) => {
            let mut arms = flatten_any_union(lhs);
            arms.push(rhs);
            arms
        }
        _ => vec![expr],
    }
}

/// Map each function parameter to its (already-elaborated) domain set
/// expression. Mirrors `ast::param_set_exprs`'s arity disambiguation exactly,
/// operating on `CartesianProduct` (the disambiguated variant) instead of
/// `BinOp::Mul`.
pub fn sem_param_set_exprs(
    domain: Option<&SemExpr>,
    n_params: usize,
) -> Result<Vec<&SemExpr>, String> {
    match domain {
        None if n_params == 0 => Ok(vec![]),
        None => Err(format!(
            "domain has 0 parts but function has {n_params} parameters"
        )),
        Some(domain_expr) => {
            let parts = flatten_cartesian_product(domain_expr);
            if parts.len() == n_params {
                Ok(parts)
            } else if n_params == 1 {
                Ok(vec![domain_expr])
            } else {
                Err(format!(
                    "domain arity {} doesn't match parameter count {} \
                     (if you're trying to destructure a vector `X*` into per-element \
                     parameters, e.g. `foo(x, y)` on a `Nat*` domain, that isn't \
                     supported yet — only a Cartesian-product tuple domain can bind \
                     multiple parameters)",
                    parts.len(),
                    n_params
                ))
            }
        }
    }
}

/// True if the range expression can produce a failure value at runtime.
/// Mirrors `codegen::range_contains_fail`, operating on the disambiguated
/// `CartesianProduct` variant (the elaborated form of `Fail * Y`, desugared
/// from `!! Y`) instead of `BinOp::Mul`.
pub fn range_contains_fail(range: &SemExpr) -> bool {
    match &range.kind {
        SemExprKind::Var(sym) => sym.0 == "Fail",
        SemExprKind::BinOp {
            op: BinOp::Union,
            lhs,
            rhs,
        } => range_contains_fail(lhs) || range_contains_fail(rhs),
        SemExprKind::CartesianProduct(lhs, _) => {
            matches!(&lhs.kind, SemExprKind::Var(sym) if sym.0 == "Fail")
        }
        _ => false,
    }
}

/// Collect all names assigned (by `mut` or reassignment) anywhere inside
/// `stmts`, recursively through nested blocks and loops. Mirrors
/// `ast::collect_loop_modified`, operating on `SemStmt`.
pub fn collect_loop_modified(stmts: &[SemStmt]) -> std::collections::HashSet<Symbol> {
    let mut names = std::collections::HashSet::new();
    collect_loop_modified_rec(stmts, &mut names);
    names
}

fn collect_loop_modified_rec(stmts: &[SemStmt], names: &mut std::collections::HashSet<Symbol>) {
    for stmt in stmts {
        match stmt {
            SemStmt::MutLet { name, .. } | SemStmt::Assign { name, .. } => {
                names.insert(name.clone());
            }
            SemStmt::DestructMutLet { bindings, .. } => {
                for b in bindings {
                    names.insert(b.name.clone());
                }
            }
            SemStmt::DestructAssign {
                names: dest_names, ..
            } => {
                for n in dest_names {
                    names.insert(n.clone());
                }
            }
            SemStmt::While { body, .. } | SemStmt::ForIn { body, .. } => {
                collect_loop_modified_rec(body, names)
            }
            SemStmt::Block(inner) => collect_loop_modified_rec(inner, names),
            _ => {}
        }
    }
}

// ── Span-free constructors for tests and hand-built SemanticTrees ──────────
//
// Mirrors `ast::Expr`'s own span-free constructors. Unlike the AST versions,
// these require an explicit Kind for anything beyond simple arithmetic —
// there's no elaboration pass to infer it from context when a tree is built
// by hand.

impl SemExpr {
    pub fn new(kind: SemExprKind, kind_of: Kind, span: Span) -> Self {
        Self {
            kind,
            kind_of,
            span,
        }
    }

    pub fn int(n: i64) -> Self {
        Self::new(SemExprKind::IntLit(n), Kind::Int, Span::dummy())
    }

    pub fn bool(b: bool) -> Self {
        Self::new(SemExprKind::BoolLit(b), Kind::Bool, Span::dummy())
    }

    pub fn var(name: &str, kind_of: Kind) -> Self {
        Self::new(SemExprKind::Var(Symbol::new(name)), kind_of, Span::dummy())
    }

    /// Value-position binary operator — `Add`/`Sub`/`Mul`/`Div` become their
    /// arithmetic variant (never the set-position `DisjointUnion`/etc.);
    /// comparisons and `and`/`or` produce `Bool`. Other operators need an
    /// explicit Kind context this constructor can't infer — use `new` directly.
    pub fn binop(op: BinOp, lhs: SemExpr, rhs: SemExpr) -> Self {
        let span = Span::dummy();
        match op {
            BinOp::Add => Self::new(
                SemExprKind::Add(Box::new(lhs), Box::new(rhs)),
                Kind::Int,
                span,
            ),
            BinOp::Sub => Self::new(
                SemExprKind::Sub(Box::new(lhs), Box::new(rhs)),
                Kind::Int,
                span,
            ),
            BinOp::Mul => Self::new(
                SemExprKind::Mul(Box::new(lhs), Box::new(rhs)),
                Kind::Int,
                span,
            ),
            BinOp::Div => Self::new(
                SemExprKind::Div(Box::new(lhs), Box::new(rhs)),
                Kind::Int,
                span,
            ),
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or => Self::new(
                SemExprKind::BinOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                Kind::Bool,
                span,
            ),
            _ => panic!(
                "SemExpr::binop: `{op}` needs an explicit kind_of (set-position/`in`/`++` \
                 operator) — use SemExpr::new directly"
            ),
        }
    }

    pub fn unop(op: UnOp, expr: SemExpr) -> Self {
        let kind_of = match op {
            UnOp::Neg => Kind::Int,
            UnOp::Not => Kind::Bool,
        };
        Self::new(
            SemExprKind::UnOp {
                op,
                expr: Box::new(expr),
            },
            kind_of,
            Span::dummy(),
        )
    }

    pub fn call(callee: &str, args: Vec<SemExpr>, return_kind: Kind) -> Self {
        Self::new(
            SemExprKind::Call {
                callee: Symbol::new(callee),
                args,
            },
            return_kind,
            Span::dummy(),
        )
    }
}

// ── Display ──────────────────────────────────────────────────────────────────
//
// Mirrors `ast::Expr`'s Display exactly (used in solver counterexample/error
// messages, e.g. "not in {constraint}"), so a printed SemExpr looks identical
// to the Cantor source it was elaborated from — regardless of which
// `SemExprKind` variant resolved `+ - * /` for it.

impl std::fmt::Display for SemExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// Precedence tier — higher number binds tighter. Mirrors `ast::binop_prec`;
/// `DisjointUnion`/`SetDifference`/`CartesianProduct`/`SetQuotient` use the
/// same tier as `+`/`-`/`*`/`/` since they're the same source operator.
fn sem_binop_prec(op: &BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq
        | BinOp::Ne
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge
        | BinOp::In
        | BinOp::NotIn => 3,
        BinOp::Union => 4,
        BinOp::SymDiff => 5,
        BinOp::Intersect => 6,
        BinOp::Add | BinOp::Sub | BinOp::Concat => 7,
        BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Quot => 8,
    }
}

/// If `kind` is (or resolves to) a binary operator node, return the `BinOp`
/// to use for its display symbol/precedence, plus its two operands.
fn as_binop(kind: &SemExprKind) -> Option<(BinOp, &SemExpr, &SemExpr)> {
    match kind {
        SemExprKind::Add(l, r) | SemExprKind::DisjointUnion(l, r) => Some((BinOp::Add, l, r)),
        SemExprKind::Sub(l, r) | SemExprKind::SetDifference(l, r) => Some((BinOp::Sub, l, r)),
        SemExprKind::Mul(l, r) | SemExprKind::CartesianProduct(l, r) => Some((BinOp::Mul, l, r)),
        SemExprKind::Div(l, r) | SemExprKind::SetQuotient(l, r) => Some((BinOp::Div, l, r)),
        SemExprKind::BinOp { op, lhs, rhs } => Some((*op, lhs, rhs)),
        _ => None,
    }
}

impl std::fmt::Display for SemExprKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some((op, lhs, rhs)) = as_binop(self) {
            let lhs_needs_parens = as_binop(&lhs.kind)
                .is_some_and(|(child_op, ..)| sem_binop_prec(&child_op) < sem_binop_prec(&op));
            let rhs_needs_parens = as_binop(&rhs.kind)
                .is_some_and(|(child_op, ..)| sem_binop_prec(&child_op) <= sem_binop_prec(&op));
            let lhs_str = if lhs_needs_parens {
                format!("({lhs})")
            } else {
                format!("{lhs}")
            };
            let rhs_str = if rhs_needs_parens {
                format!("({rhs})")
            } else {
                format!("{rhs}")
            };
            return write!(f, "{lhs_str} {op} {rhs_str}");
        }
        match self {
            SemExprKind::IntLit(n) => write!(f, "{n}"),
            SemExprKind::BoolLit(b) => write!(f, "{b}"),
            SemExprKind::Var(sym) => write!(f, "{sym}"),
            SemExprKind::UnOp { op, expr } => match op {
                UnOp::Neg => write!(f, "-{expr}"),
                UnOp::Not => write!(f, "not {expr}"),
            },
            SemExprKind::Call { callee, args } => {
                write!(f, "{callee}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            SemExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                write!(f, "if {cond} then {then_expr} else {else_expr}")
            }
            SemExprKind::SetLit(elements) => {
                write!(f, "{{")?;
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, "}}")
            }
            SemExprKind::Try(inner) => write!(f, "{inner}?"),
            SemExprKind::FailLit => f.write_str("fail"),
            SemExprKind::FailWith(expr) => write!(f, "fail {expr}"),
            SemExprKind::Comprehension {
                output,
                var,
                source,
                filter,
            } => {
                write!(f, "{{{output} for {var} in {source}")?;
                if let Some(pred) = filter {
                    write!(f, " if {pred}")?;
                }
                write!(f, "}}")
            }
            SemExprKind::Tuple(elems) => {
                write!(f, "(")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, ")")
            }
            SemExprKind::Proj { base, index } => write!(f, "{base}.{index}"),
            SemExprKind::Index { base, index } => write!(f, "{base}[{index}]"),
            SemExprKind::KleeneStar(inner) => match &inner.kind {
                SemExprKind::Var(_) => write!(f, "{inner}*"),
                _ => write!(f, "({inner})*"),
            },
            // Handled by the `as_binop` early-return above.
            SemExprKind::Add(..)
            | SemExprKind::Sub(..)
            | SemExprKind::Mul(..)
            | SemExprKind::Div(..)
            | SemExprKind::DisjointUnion(..)
            | SemExprKind::SetDifference(..)
            | SemExprKind::CartesianProduct(..)
            | SemExprKind::SetQuotient(..)
            | SemExprKind::BinOp { .. } => unreachable!("handled by as_binop above"),
        }
    }
}
