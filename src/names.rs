//! Naming convention checker (§2a of the design doc).
//!
//! Two rules are enforced after parsing, before SMT checking:
//!
//! 1. **Definition names must start with a lowercase letter.**
//!    Applies to: function names, constant names, parameter names, `mut` locals.
//!
//! 2. **Identifiers in domain/range constraints must start with an uppercase letter.**
//!    Applies to: domain and range set expressions in function signatures, and
//!    the set annotation in constant definitions.
//!    (The RHS of `in`/`not in` in expression bodies is deliberately unchecked
//!    because it accepts both uppercase named sets and lowercase runtime sets.)
//!
//! All violations are collected before returning so the developer sees every
//! problem at once rather than fixing them one at a time.

use crate::{
    ast::{Expr, ExprKind, FunctionBody, FunctionDef, Item, NameDef, Stmt},
    error::CompileError,
    span::Span,
};

// ── Compile-time set predicate ────────────────────────────────────────────────

/// Returns `true` when every variable reference in `expr` is uppercase,
/// meaning the expression is statically materializable at compile time.
/// Set literals and numeric/boolean literals are always compile-time.
fn is_compile_time_value(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Var(sym) => starts_uppercase(&sym.0),
        ExprKind::SetLit(_) | ExprKind::IntLit(_) | ExprKind::BoolLit(_) => true,
        ExprKind::BinOp { lhs, rhs, .. } => {
            is_compile_time_value(lhs) && is_compile_time_value(rhs)
        }
        ExprKind::UnOp { expr: inner, .. } => is_compile_time_value(inner),
        _ => false,
    }
}

/// Check naming conventions across an entire parsed file.
/// Returns all violations found (empty Vec = no errors).
pub fn check_names(items: &[Item]) -> Vec<CompileError> {
    let mut errors = Vec::new();
    for item in items {
        match item {
            Item::FunctionDef(def) => check_function(def, &mut errors),
            Item::NameDef(def)     => check_name_def(def, &mut errors),
        }
    }
    errors
}

// ── Per-item checks ───────────────────────────────────────────────────────────

fn check_function(def: &FunctionDef, errors: &mut Vec<CompileError>) {
    must_be_lowercase(&def.name.0, def.span, errors);

    for param in &def.params {
        must_be_lowercase(&param.name.0, param.span, errors);
    }

    for sig in &def.sigs {
        if let Some(domain) = &sig.domain {
            vars_must_be_uppercase(domain, errors);
        }
        vars_must_be_uppercase(&sig.range, errors);
    }

    if let FunctionBody::Block(stmts) = &def.body {
        check_stmts(stmts, errors);
    }
}

fn check_name_def(def: &NameDef, errors: &mut Vec<CompileError>) {
    if let Some(ty) = &def.ty {
        // Annotated form (`name : Set = value`): name must be lowercase, annotation uppercase.
        must_be_lowercase(&def.name.0, def.span, errors);
        vars_must_be_uppercase(ty, errors);
    } else {
        // Unannotated form (`Name = [alias|distinct] value`): name must be uppercase,
        // value is a set expression so its vars must also be uppercase.
        if !starts_uppercase(&def.name.0) {
            errors.push(CompileError::NamingConvention {
                message: format!(
                    "`{}` is a set definition and must start with an uppercase letter \
                     (compile-time set names must be uppercase per §2a)",
                    def.name
                ),
                span: def.span,
            });
        }
        vars_must_be_uppercase(&def.value, errors);
    }
}

fn check_stmts(stmts: &[Stmt], errors: &mut Vec<CompileError>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, span, .. } | Stmt::MutLet { name, span, .. } => must_be_lowercase(&name.0, *span, errors),
            Stmt::DestructLet { bindings, span, .. } | Stmt::DestructMutLet { bindings, span, .. } => {
                for binding in bindings {
                    must_be_lowercase(&binding.name.0, *span, errors);
                }
            }
            Stmt::Block(inner)              => check_stmts(inner, errors),
            Stmt::While { body, .. }        => check_stmts(body, errors),
            Stmt::ForIn { var, set, body, span, .. } => {
                // Uppercase loop variable promises compile-time values; the
                // iterable must be statically materializable to honour that promise.
                if starts_uppercase(&var.0) && !is_compile_time_value(set) {
                    errors.push(CompileError::NamingConvention {
                        message: format!(
                            "`{}` is uppercase, which promises a compile-time value; \
                             the iterable must be a set literal or an uppercase-named \
                             set (use lowercase `{}` for a runtime iterable)",
                            var.0,
                            var.0.chars().next().map(|c| {
                                let mut s = c.to_lowercase().to_string();
                                s.push_str(&var.0[c.len_utf8()..]);
                                s
                            }).unwrap_or_default(),
                        ),
                        span: *span,
                    });
                }
                check_stmts(body, errors);
            }
            _ => {}
        }
    }
}

// ── Leaf checks ───────────────────────────────────────────────────────────────

fn must_be_lowercase(name: &str, span: Span, errors: &mut Vec<CompileError>) {
    if starts_uppercase(name) {
        errors.push(CompileError::NamingConvention {
            message: format!(
                "`{name}` must start with a lowercase letter \
                 (uppercase names are reserved for compile-time set names)"
            ),
            span,
        });
    }
}

/// Walk a set expression and require every `Var` node to start uppercase.
/// Recurses into binary set operations and unary negation; stops at
/// `SetLit` elements (which are integer/boolean values, not set names).
fn vars_must_be_uppercase(expr: &Expr, errors: &mut Vec<CompileError>) {
    match &expr.kind {
        ExprKind::Var(sym) => {
            if starts_lowercase(&sym.0) {
                errors.push(CompileError::NamingConvention {
                    message: format!(
                        "`{}` in a domain/range constraint must start with an uppercase letter \
                         (only compile-time named sets are allowed here; \
                         runtime sets cannot appear in domain/range constraints)",
                        sym.0
                    ),
                    span: expr.span,
                });
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            vars_must_be_uppercase(lhs, errors);
            vars_must_be_uppercase(rhs, errors);
        }
        ExprKind::UnOp { expr: inner, .. } => vars_must_be_uppercase(inner, errors),
        // SetLit elements are integer constants — no name check needed.
        // IntLit, BoolLit — fine as bare elements of a set literal.
        _ => {}
    }
}

// ── Utilities ─────────────────────────────────────────────────────────────────

fn starts_uppercase(name: &str) -> bool {
    name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false)
}

fn starts_lowercase(name: &str) -> bool {
    name.chars().next().map(|c| c.is_lowercase()).unwrap_or(false)
}
