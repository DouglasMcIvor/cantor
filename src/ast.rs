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

    pub fn try_op(expr: Expr) -> Self {
        Self::new(ExprKind::Try(Box::new(expr)), Span::dummy())
    }

    pub fn fail_lit() -> Self {
        Self::new(ExprKind::FailLit, Span::dummy())
    }

    pub fn fail_with(expr: Expr) -> Self {
        Self::new(ExprKind::FailWith(Box::new(expr)), Span::dummy())
    }

    pub fn comprehension(output: Expr, var: &str, source: Expr, filter: Option<Expr>) -> Self {
        Self::new(
            ExprKind::Comprehension {
                output: Box::new(output),
                var: Symbol::new(var),
                source: Box::new(source),
                filter: filter.map(Box::new),
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
    /// `{ expr, expr, … }` — explicit set literal; used in signature position.
    SetLit(Vec<Expr>),
    /// `expr?` — propagate `Fail` from a fallible call up to the caller.
    Try(Box<Expr>),
    /// Bare `fail` — the singleton failure value (member of `Fail = {fail}`).
    FailLit,
    /// `fail expr` — construct a tagged failure with payload `expr`.
    /// At runtime encoded as `FAIL_SENTINEL + expr + 1` so the caller's `?`
    /// can distinguish it from a success value even when the payload is
    /// numerically equal to a valid success value.
    FailWith(Box<Expr>),
    /// `{ output for var in source }` or `{ output for var in source if filter }`
    Comprehension {
        output: Box<Expr>,
        var: Symbol,
        source: Box<Expr>,
        filter: Option<Box<Expr>>,
    },
    /// `(e0, e1, …)` — anonymous product value (tuple).
    Tuple(Vec<Expr>),
    /// `expr.N` — positional projection of element N from a tuple (N is a compile-time literal).
    Proj { base: Box<Expr>, index: usize },
    /// `expr[index]` — runtime indexing into a vector (X* value).
    /// Only valid when `base` has kind `Kind::Vector`; compile-time-literal indices are
    /// always desugared to `Proj` at parse time so `index` is always a runtime value here.
    Index { base: Box<Expr>, index: Box<Expr> },
    /// `X*` — Kleene star in set position: the set of all finite sequences of elements of X.
    /// Parsed as a postfix `*` when no expression follows, e.g. `Nat*` or `(Int - {0})*`.
    KleeneStar(Box<Expr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic / set constructors (context disambiguates)
    Add, // arithmetic addition in value position; disjoint union in set position (A + B requires A ∩ B = ∅)
    Sub, // arithmetic subtraction in value position; set difference in set position
    Mul, // arithmetic multiplication in value position; Cartesian product in set position
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
    Union,      // |  — `X !! Y` desugars to `X | (Fail * Y)` at parse time
    Intersect,  // &
    SymDiff,    // ^
    // Vector operations
    Concat,     // ++ — concatenate two vectors (X* ++ X* -> X*)
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

/// One binding in a destructuring pattern, e.g. the `x : Int` in `x : Int, y = (...)`.
#[derive(Debug, Clone)]
pub struct DestructBinding {
    pub name: Symbol,
    /// Optional per-element set constraint (e.g. `: Int`). None means unconstrained.
    pub constraint: Option<Expr>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    /// `x: Set = expr` — introduce an immutable local with a constraint check.
    ///
    /// The `constraint` is verified once at the binding site; the name may not
    /// appear on the left-hand side of `:=`.
    Let { name: Symbol, constraint: Expr, value: Expr, span: Span },
    /// `mut x: Set = expr` — introduce a new mutable local with invariant.
    ///
    /// The `constraint` is the declared set the variable must remain in through
    /// every assignment.  The solver uses it as the loop invariant when the
    /// variable is modified inside a `while` body.
    MutLet { name: Symbol, constraint: Expr, value: Expr, span: Span },
    /// `x := expr` — reassign an existing mutable (semantic analysis validates).
    Assign { name: Symbol, value: Expr, span: Span },
    /// `x, y = (e0, e1)` or `x : Int, y : Nat = (e0, e1)` — immutable destructure.
    ///
    /// `tuple_constraint` is `Some` for the `x, y : Int * Nat = (...)` form and
    /// `None` for the per-element constraint form.  Currently the parser always
    /// emits `None`; tuple-level constraints are a planned future extension.
    DestructLet { bindings: Vec<DestructBinding>, tuple_constraint: Option<Expr>, value: Expr, span: Span },
    /// `mut a : Int, b : Nat = (e0, e1)` — mutable destructure; `mut` applies to all bindings.
    DestructMutLet { bindings: Vec<DestructBinding>, tuple_constraint: Option<Expr>, value: Expr, span: Span },
    /// `a, b := (e0, e1)` — destructuring reassignment; all names must already be `mut`.
    DestructAssign { names: Vec<Symbol>, value: Expr, span: Span },
    /// `require predicate` — static proof obligation; compile error if unprovable.
    Require { predicate: Expr, span: Span },
    /// `assert predicate` — graduated: elide if proved, compile error if disproved,
    /// runtime check + Class 1 error if unknown.
    /// Optional `else` clause overrides what is returned when the check fails:
    ///   - `else fail expr` — return the offset-encoded failure value
    ///   - `else return expr` — return `expr` directly (early exit, success path)
    Assert { predicate: Expr, else_clause: Option<AssertElse>, span: Span },
    /// `assume predicate` — add predicate as a solver fact with no proof or runtime check.
    Assume { predicate: Expr, span: Span },
    /// Bare expression; the last `Expr` stmt in a block is the return value.
    Expr(Expr),
    /// Nested `{ stmts }` block — introduces a new scope.
    Block(Vec<Stmt>),
    /// `while cond { stmts }` — loop while condition holds.
    While { cond: Expr, body: Vec<Stmt>, span: Span },
    /// `for x in S { stmts }` — iterate over each element of the set S.
    ForIn { var: Symbol, set: Expr, body: Vec<Stmt>, span: Span },
    /// `return expr` — early return from a block body.
    Return { value: Expr, span: Span },
}

/// The alternative action in `assert pred else <clause>`.
#[derive(Debug, Clone)]
pub enum AssertElse {
    /// `else fail expr` — return `fail expr` (offset-encoded failure payload).
    FailWith(Expr),
    /// `else return expr` — early-return `expr` as a success value.
    Return(Expr),
}

// ── Set-expression AST utilities ─────────────────────────────────────────────

/// Flatten a left-associative `A * B * C` product into `[A, B, C]`.
pub fn flatten_domain(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Mul, lhs, rhs } => {
            let mut parts = flatten_domain(lhs);
            parts.push(rhs);
            parts
        }
        _ => vec![expr],
    }
}

/// Flatten a left-associated disjoint union `((A + B) + C)` into `[A, B, C]`.
pub fn flatten_disjoint_union(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::BinOp { op: BinOp::Add, lhs, rhs } => {
            let mut arms = flatten_disjoint_union(lhs);
            arms.extend(flatten_disjoint_union(rhs));
            arms
        }
        _ => vec![expr],
    }
}

/// Map each function parameter to its set expression, implementing the
/// arity disambiguation rule:
///
/// - `parts.len() == n_params` → N scalar params (each part is one param's set).
/// - `n_params == 1` and `parts.len() > 1` → the single param is a tuple whose
///   set is the entire domain expression.
/// - Otherwise → arity error.
pub fn param_set_exprs<'a>(domain: Option<&'a Expr>, n_params: usize) -> Result<Vec<&'a Expr>, String> {
    match domain {
        None if n_params == 0 => Ok(vec![]),
        None => Err(format!("domain has 0 parts but function has {n_params} parameters")),
        Some(domain_expr) => {
            let parts = flatten_domain(domain_expr);
            if parts.len() == n_params {
                Ok(parts)
            } else if n_params == 1 {
                // Single tuple parameter covering the whole product domain.
                Ok(vec![domain_expr])
            } else {
                Err(format!(
                    "domain arity {} doesn't match parameter count {}",
                    parts.len(), n_params
                ))
            }
        }
    }
}

// ── Loop variable collection ──────────────────────────────────────────────────

/// Collect all names that are assigned (by `mut` or reassignment) anywhere
/// inside `stmts`, recursively through nested blocks and while loops.
///
/// Used by both the solver (to invalidate loop-modified variables) and the
/// codegen (to decide which variables need alloca-backed storage for loops).
pub fn collect_loop_modified(stmts: &[Stmt]) -> std::collections::HashSet<Symbol> {
    let mut names = std::collections::HashSet::new();
    collect_loop_modified_rec(stmts, &mut names);
    names
}

fn collect_loop_modified_rec(stmts: &[Stmt], names: &mut std::collections::HashSet<Symbol>) {
    for stmt in stmts {
        match stmt {
            Stmt::MutLet { name, .. } | Stmt::Assign { name, .. } => { names.insert(name.clone()); }
            Stmt::DestructMutLet { bindings, .. } => {
                for b in bindings { names.insert(b.name.clone()); }
            }
            Stmt::DestructAssign { names: dest_names, .. } => {
                for n in dest_names { names.insert(n.clone()); }
            }
            Stmt::While { body, .. } | Stmt::ForIn { body, .. } => collect_loop_modified_rec(body, names),
            Stmt::Block(inner) => collect_loop_modified_rec(inner, names),
            _ => {}
        }
    }
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

// ── Named definitions ─────────────────────────────────────────────────────────

/// Whether a named definition is a transparent alias or introduces a new
/// disjoint/opaque identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefKind {
    /// Default — transparent to the solver.
    /// `x in Name` expands to `x in value` (set position) or inlines `value`
    /// (value position).
    Alias,
    /// `Name = distinct expr` — new identity disjoint from its basis.
    /// The solver treats membership as opaque; `x in Name` returns Unknown.
    Distinct,
}

/// A top-level named definition: `name [: ty] = [alias|distinct] value`.
///
/// Covers both what were previously `ConstDef` and `SetDef`:
///
/// - `pi : Nat = 314` — annotated constant (ty = Some(Nat), kind = Alias)
/// - `Colour = {1, 2, 3}` — unannotated set alias (ty = None, kind = Alias)
/// - `Litre = distinct Nat` — opaque distinct set (ty = None, kind = Distinct)
///
/// Naming convention (§2a): lowercase names are value constants; uppercase
/// names are compile-time set names.  Both use the same AST node.
#[derive(Debug, Clone)]
pub struct NameDef {
    pub name: Symbol,
    pub kind: DefKind,
    /// Optional type annotation — present for `name : Set = expr` form.
    /// When present, the solver verifies `value ∈ ty`.
    pub ty: Option<Expr>,
    pub value: Expr,
    pub span: Span,
}

// ── Top-level items ───────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub enum Item {
    FunctionDef(FunctionDef),
    NameDef(NameDef),
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
            Self::Try(inner) => write!(f, "{inner}?"),
            Self::FailLit => f.write_str("fail"),
            Self::FailWith(expr) => write!(f, "fail {expr}"),
            Self::Comprehension { output, var, source, filter } => {
                write!(f, "{{{output} for {var} in {source}")?;
                if let Some(pred) = filter {
                    write!(f, " if {pred}")?;
                }
                write!(f, "}}")
            }
            Self::Tuple(elems) => {
                write!(f, "(")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{e}")?;
                }
                write!(f, ")")
            }
            Self::Proj { base, index } => write!(f, "{base}.{index}"),
            Self::Index { base, index } => write!(f, "{base}[{index}]"),
            Self::KleeneStar(inner) => match &inner.kind {
                // Simple set names don't need parens: Nat* not (Nat)*.
                ExprKind::Var(_) => write!(f, "{inner}*"),
                _ => write!(f, "({inner})*"),
            },
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
        | BinOp::In | BinOp::NotIn              => 3,
        BinOp::Union                            => 4,
        BinOp::SymDiff                          => 5,
        BinOp::Intersect                        => 6,
        BinOp::Add | BinOp::Sub | BinOp::Concat => 7,
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
            Self::Union      => "|",
            Self::Intersect  => "&",
            Self::SymDiff    => "^",
            Self::And        => "and",
            Self::Or         => "or",
            Self::Concat     => "++",
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
