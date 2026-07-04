//! Statement and block parsing, including destructuring `let`/`mut`/reassignment.

use super::Parser;
use super::lexer::Token;

use crate::{
    ast::{AssertElse, DestructBinding, Stmt},
    error::CompileError,
    span::Span,
};

impl<'src> Parser<'src> {
    // ── Imperative block ──────────────────────────────────────────────────────

    /// Parse `{ stmt* }`, returning the statement list.
    pub(super) fn parse_block(&mut self) -> Result<Vec<Stmt>, CompileError> {
        self.expect(&Token::LBrace)?;
        self.skip_newlines()?;
        let mut stmts = Vec::new();
        while self.peek() != &Token::RBrace && self.peek() != &Token::Eof {
            stmts.push(self.parse_stmt()?);
            self.skip_newlines()?;
        }
        self.expect(&Token::RBrace)?;
        Ok(stmts)
    }

    pub(super) fn parse_stmt(&mut self) -> Result<Stmt, CompileError> {
        let span = self.peek_span();
        match self.peek().clone() {
            Token::Mut => {
                self.advance()?;
                // `mut a, b = ...` — destructuring detected via 2-token lookahead.
                if matches!(self.peek(), Token::Ident(_)) && self.peek2() == &Token::Comma {
                    return self.parse_destruct_mut_let(span);
                }
                let name = self.expect_ident()?;
                self.expect(&Token::Colon)?;
                let constraint = self.parse_set_expr()?;
                // `mut a : Int, b : Nat = ...` — comma after constraint reveals destructuring.
                if self.peek() == &Token::Comma {
                    self.advance()?;
                    let first = DestructBinding {
                        name,
                        constraint: Some(constraint),
                    };
                    let mut rest = self.parse_destruct_binding_list()?;
                    rest.insert(0, first);
                    self.expect(&Token::Eq)?;
                    let value = self.parse_expr(0)?;
                    return Ok(Stmt::DestructMutLet {
                        bindings: rest,
                        tuple_constraint: None,
                        value,
                        span,
                    });
                }
                self.expect(&Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::MutLet {
                    name,
                    constraint,
                    value,
                    span,
                })
            }
            Token::Require => {
                self.advance()?;
                let predicate = self.parse_expr(0)?;
                Ok(Stmt::Require { predicate, span })
            }
            Token::Assert => {
                self.advance()?;
                let predicate = self.parse_expr(0)?;
                self.skip_newlines()?;
                let else_clause = if self.peek() == &Token::Else {
                    self.advance()?;
                    match self.peek().clone() {
                        Token::Fail => {
                            self.advance()?;
                            let expr = self.parse_expr(0)?;
                            Some(AssertElse::FailWith(expr))
                        }
                        Token::Return => {
                            self.advance()?;
                            let expr = self.parse_expr(0)?;
                            Some(AssertElse::Return(expr))
                        }
                        other => {
                            let bad_span = self.peek_span();
                            return Err(CompileError::UnexpectedToken {
                                expected: "`fail` or `return`".into(),
                                found: other.to_string(),
                                span: bad_span,
                            });
                        }
                    }
                } else {
                    None
                };
                Ok(Stmt::Assert {
                    predicate,
                    else_clause,
                    span,
                })
            }
            Token::Assume => {
                self.advance()?;
                let predicate = self.parse_expr(0)?;
                Ok(Stmt::Assume { predicate, span })
            }
            Token::While => {
                self.advance()?;
                let cond = self.parse_expr(0)?;
                self.skip_newlines()?;
                let body = self.parse_block()?;
                Ok(Stmt::While { cond, body, span })
            }
            Token::For => {
                self.advance()?;
                let var = self.expect_ident()?;
                self.expect(&Token::In)?;
                let set = self.parse_set_expr()?;
                self.skip_newlines()?;
                let body = self.parse_block()?;
                Ok(Stmt::ForIn {
                    var,
                    set,
                    body,
                    span,
                })
            }
            Token::Return => {
                self.advance()?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::Return { value, span })
            }
            Token::LBrace => Ok(Stmt::Block(self.parse_block()?)),
            // `ident, ...` → destructuring let or reassignment.
            // Must come before the `:=` and `:` arms so `x, y = ...` is caught here.
            Token::Ident(_) if self.peek2() == &Token::Comma => {
                self.parse_destruct_let_or_assign(span)
            }
            // `ident :=` → reassignment of a `mut` variable
            Token::Ident(_) if self.peek2() == &Token::ColonEq => {
                let name = self.expect_ident()?;
                self.expect(&Token::ColonEq)?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::Assign { name, value, span })
            }
            // `ident : Set = expr` or `x : Int, y : Nat = expr` (destructuring with constraints)
            Token::Ident(_) if self.peek2() == &Token::Colon => {
                let name = self.expect_ident()?;
                self.expect(&Token::Colon)?;
                let constraint = self.parse_set_expr()?;
                // A comma after the constraint reveals a destructuring binding list.
                if self.peek() == &Token::Comma {
                    self.advance()?;
                    let first = DestructBinding {
                        name,
                        constraint: Some(constraint),
                    };
                    let mut rest = self.parse_destruct_binding_list()?;
                    rest.insert(0, first);
                    self.expect(&Token::Eq)?;
                    let value = self.parse_expr(0)?;
                    return Ok(Stmt::DestructLet {
                        bindings: rest,
                        tuple_constraint: None,
                        value,
                        span,
                    });
                }
                self.expect(&Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::Let {
                    name,
                    constraint,
                    value,
                    span,
                })
            }
            _ => Ok(Stmt::Expr(self.parse_expr(0)?)),
        }
    }

    // ── Destructuring helpers ─────────────────────────────────────────────────

    /// Parse a comma-separated list of `name [: constraint]` bindings.
    ///
    /// Stops when the next token is not a comma after a binding name.
    fn parse_destruct_binding_list(&mut self) -> Result<Vec<DestructBinding>, CompileError> {
        let mut bindings = Vec::new();
        loop {
            let name = self.expect_ident()?;
            let constraint = if self.peek() == &Token::Colon {
                self.advance()?;
                Some(self.parse_set_expr()?)
            } else {
                None
            };
            bindings.push(DestructBinding { name, constraint });
            if self.peek() != &Token::Comma {
                break;
            }
            self.advance()?; // consume comma
        }
        Ok(bindings)
    }

    /// Parse a destructuring let (`x, y = ...`) or reassign (`a, b := ...`).
    ///
    /// Called after detecting `Ident, Comma` in `parse_stmt`.
    fn parse_destruct_let_or_assign(&mut self, span: Span) -> Result<Stmt, CompileError> {
        let bindings = self.parse_destruct_binding_list()?;
        match self.peek().clone() {
            Token::ColonEq => {
                self.advance()?;
                // Constraints are not allowed in reassignment — the names must already be declared.
                for b in &bindings {
                    if b.constraint.is_some() {
                        return Err(CompileError::UnexpectedToken {
                            expected: "`:=` after plain names (set constraints belong in the initial `mut` declaration, not in reassignment)".into(),
                            found: "`:=` after a `:` constraint".into(),
                            span,
                        });
                    }
                }
                let names = bindings.into_iter().map(|b| b.name).collect();
                let value = self.parse_expr(0)?;
                Ok(Stmt::DestructAssign { names, value, span })
            }
            Token::Eq => {
                self.advance()?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::DestructLet {
                    bindings,
                    tuple_constraint: None,
                    value,
                    span,
                })
            }
            other => {
                let bad_span = self.peek_span();
                Err(CompileError::UnexpectedToken {
                    expected: "`=` or `:=`".into(),
                    found: other.to_string(),
                    span: bad_span,
                })
            }
        }
    }

    /// Parse `mut a : Int, b = (...)` — destructuring with all bindings mutable.
    ///
    /// Called after `Mut` has already been consumed and `Ident, Comma` detected.
    fn parse_destruct_mut_let(&mut self, span: Span) -> Result<Stmt, CompileError> {
        let bindings = self.parse_destruct_binding_list()?;
        self.expect(&Token::Eq)?;
        let value = self.parse_expr(0)?;
        Ok(Stmt::DestructMutLet {
            bindings,
            tuple_constraint: None,
            value,
            span,
        })
    }
}
