pub mod lexer;

use lexer::{Lexer, Token};

use crate::{
    ast::{AssertElse, BinOp, DefKind, DestructBinding, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item, NameDef, Param, Stmt, UnOp},
    error::CompileError,
    span::{Span, Symbol},
};

/// Recursive-descent / Pratt parser for Cantor.
///
/// Two tokens of lookahead so that `not in` (two-token infix operator) and
/// `ident =` (assignment statement) can be recognised without backtracking.
pub struct Parser<'src> {
    lexer: Lexer<'src>,
    peek0: (Token, Span),
    peek1: (Token, Span),
}

impl<'src> Parser<'src> {
    pub fn new(src: &'src str) -> Result<Self, CompileError> {
        let mut lexer = Lexer::new(src);
        let peek0 = lexer.next_token()?;
        let peek1 = lexer.next_token()?;
        Ok(Self { lexer, peek0, peek1 })
    }

    // ── Lookahead ─────────────────────────────────────────────────────────────

    fn peek(&self) -> &Token {
        &self.peek0.0
    }

    fn peek_span(&self) -> Span {
        self.peek0.1
    }

    fn peek2(&self) -> &Token {
        &self.peek1.0
    }

    fn advance(&mut self) -> Result<(Token, Span), CompileError> {
        let new_peek1 = self.lexer.next_token()?;
        let old_peek1 = std::mem::replace(&mut self.peek1, new_peek1);
        Ok(std::mem::replace(&mut self.peek0, old_peek1))
    }

    /// Consume all leading `Newline` tokens from the lookahead buffer.
    fn skip_newlines(&mut self) -> Result<(), CompileError> {
        while self.peek() == &Token::Newline {
            self.advance()?;
        }
        Ok(())
    }

    fn expect(&mut self, expected: &Token) -> Result<Span, CompileError> {
        let span = self.peek_span();
        let (tok, _) = self.advance()?;
        if &tok == expected {
            Ok(span)
        } else {
            Err(CompileError::UnexpectedToken {
                expected: expected.to_string(),
                found: tok.to_string(),
                span,
            })
        }
    }

    // ── Top-level file ────────────────────────────────────────────────────────

    /// Parse a whole source file as a sequence of top-level items.
    pub fn parse_file(&mut self) -> Result<Vec<Item>, CompileError> {
        let mut items = Vec::new();
        self.skip_newlines()?;
        while self.peek() != &Token::Eof {
            items.push(self.parse_item()?);
            self.skip_newlines()?;
        }
        Ok(items)
    }

    fn parse_item(&mut self) -> Result<Item, CompileError> {
        // Unannotated name def: `Name = [alias|distinct] expr`
        // Disambiguated from annotated defs and functions (which have `:` after the name)
        // by checking the second lookahead token.
        if matches!(self.peek(), Token::Ident(_)) && self.peek2() == &Token::Eq {
            return self.parse_unannotated_name_def();
        }

        let start_span = self.peek_span();
        let name = self.expect_ident()?;
        self.expect(&Token::Colon)?;

        // Determine whether this is a function or a constant.
        //
        // Grammar:
        //   function : IDENT ':' [set_expr '->'] set_expr   impl
        //   constant : IDENT ':' set_expr '=' expr
        //
        // `parse_set_expr` stops before `->` (Arrow is not an infix op), so
        // after parsing one set_expr we can check for `->` to decide.
        let (first_domain, first_range) = if self.peek() == &Token::Arrow {
            // Zero-arg function: `name : -> range`
            self.advance()?;
            (None, self.parse_set_expr()?)
        } else {
            let first_expr = self.parse_set_expr()?;
            if self.peek() == &Token::Arrow {
                // Regular function: `name : domain -> range`
                self.advance()?;
                (Some(first_expr), self.parse_set_expr()?)
            } else {
                // No `->` found → annotated name def: `name : ty = value`
                self.expect(&Token::Eq)?;
                let value = self.parse_expr(0)?;
                let end = value.span.end;
                return Ok(Item::NameDef(NameDef {
                    name,
                    kind: DefKind::Alias,
                    ty: Some(first_expr),
                    value,
                    span: Span::new(start_span.start, end),
                }));
            }
        };

        let first_sig_end = first_range.span.end;
        let first_sig = FunctionSig {
            domain: first_domain,
            range: first_range,
            span: Span::new(start_span.start, first_sig_end),
        };

        // Collect additional sig lines sharing the same name.
        let mut sigs = vec![first_sig];
        loop {
            self.skip_newlines()?;
            if !(self.peek() == &Token::Ident(name.0.clone()) && self.peek2() == &Token::Colon) {
                break;
            }
            self.advance()?; // consume repeated name
            sigs.push(self.parse_sig_tail()?);
        }

        // Implementation: `name(params) = expr`  or  `name(params) { stmts }`
        let impl_name = self.expect_ident()?;
        if impl_name.0 != name.0 {
            return Err(CompileError::UnexpectedToken {
                expected: format!("`{}` (implementation must follow its signatures)", name),
                found: format!("`{}`", impl_name),
                span: start_span,
            });
        }

        self.expect(&Token::LParen)?;
        let params = self.parse_params()?;
        self.expect(&Token::RParen)?;
        self.skip_newlines()?;

        let body = if self.peek() == &Token::Eq {
            self.advance()?;
            FunctionBody::Expr(self.parse_expr(0)?)
        } else if self.peek() == &Token::LBrace {
            FunctionBody::Block(self.parse_block()?)
        } else {
            let span = self.peek_span();
            return Err(CompileError::UnexpectedToken {
                expected: "`=` or `{`".into(),
                found: self.peek().to_string(),
                span,
            });
        };

        let end = match &body {
            FunctionBody::Expr(e) => e.span.end,
            FunctionBody::Block(_) => self.peek_span().start,
        };

        Ok(Item::FunctionDef(FunctionDef {
            name,
            sigs,
            params,
            body,
            span: Span::new(start_span.start, end),
        }))
    }

    /// Parse an unannotated name def: `Name = [alias|distinct] expr`.
    ///
    /// Called when we see `Ident '='` at the top level (peeked two tokens ahead).
    fn parse_unannotated_name_def(&mut self) -> Result<Item, CompileError> {
        let start = self.peek_span();
        let name = self.expect_ident()?;
        self.expect(&Token::Eq)?;
        let kind = match self.peek().clone() {
            Token::Distinct => { self.advance()?; DefKind::Distinct }
            Token::Alias    => { self.advance()?; DefKind::Alias }
            _               => DefKind::Alias,
        };
        let value = self.parse_set_expr()?;
        let end = value.span.end;
        Ok(Item::NameDef(NameDef { name, kind, ty: None, value, span: Span::new(start.start, end) }))
    }

    /// Parse everything after the name on a signature line: `: [domain] -> range`
    /// Domain is omitted for zero-arg functions: `name : -> Set`.
    fn parse_sig_tail(&mut self) -> Result<FunctionSig, CompileError> {
        let start = self.peek_span();
        self.expect(&Token::Colon)?;
        let domain = if self.peek() == &Token::Arrow {
            None
        } else {
            Some(self.parse_set_expr()?)
        };
        self.expect(&Token::Arrow)?;
        let range = self.parse_set_expr()?;
        let end = range.span.end;
        Ok(FunctionSig { domain, range, span: Span::new(start.start, end) })
    }

    /// Parse a set expression in signature position.
    ///
    /// For now this is just a regular expression — `*` means Cartesian product
    /// here rather than multiplication, but we record the same AST node and let
    /// the type checker disambiguate by position. Stops before `->`.
    fn parse_set_expr(&mut self) -> Result<Expr, CompileError> {
        // We parse a full expression but Arrow is not an infix operator so the
        // Pratt loop will naturally stop before `->`; the `-` in `->` is consumed
        // by the lexer as Arrow, not Minus, so there's no ambiguity.
        self.parse_expr(0)
    }

    // ── Parameters ────────────────────────────────────────────────────────────

    fn parse_params(&mut self) -> Result<Vec<Param>, CompileError> {
        let mut params = Vec::new();
        if self.peek() == &Token::RParen {
            return Ok(params);
        }
        params.push(self.parse_one_param()?);
        while self.peek() == &Token::Comma {
            self.advance()?;
            params.push(self.parse_one_param()?);
        }
        Ok(params)
    }

    fn parse_one_param(&mut self) -> Result<Param, CompileError> {
        let span = self.peek_span();
        let name = self.expect_ident()?;
        Ok(Param { name, span })
    }

    // ── Imperative block ──────────────────────────────────────────────────────

    /// Parse `{ stmt* }`, returning the statement list.
    fn parse_block(&mut self) -> Result<Vec<Stmt>, CompileError> {
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

    fn parse_stmt(&mut self) -> Result<Stmt, CompileError> {
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
                    let first = DestructBinding { name, constraint: Some(constraint) };
                    let mut rest = self.parse_destruct_binding_list()?;
                    rest.insert(0, first);
                    self.expect(&Token::Eq)?;
                    let value = self.parse_expr(0)?;
                    return Ok(Stmt::DestructMutLet { bindings: rest, tuple_constraint: None, value, span });
                }
                self.expect(&Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::MutLet { name, constraint, value, span })
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
                Ok(Stmt::Assert { predicate, else_clause, span })
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
                Ok(Stmt::ForIn { var, set, body, span })
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
                    let first = DestructBinding { name, constraint: Some(constraint) };
                    let mut rest = self.parse_destruct_binding_list()?;
                    rest.insert(0, first);
                    self.expect(&Token::Eq)?;
                    let value = self.parse_expr(0)?;
                    return Ok(Stmt::DestructLet { bindings: rest, tuple_constraint: None, value, span });
                }
                self.expect(&Token::Eq)?;
                let value = self.parse_expr(0)?;
                Ok(Stmt::Let { name, constraint, value, span })
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
                Ok(Stmt::DestructLet { bindings, tuple_constraint: None, value, span })
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
        Ok(Stmt::DestructMutLet { bindings, tuple_constraint: None, value, span })
    }

    // ── Expression (Pratt) ────────────────────────────────────────────────────

    /// Parse an expression with at least the given minimum left-binding power.
    pub fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            // Postfix `?` — highest precedence, applied immediately to lhs.
            if self.peek() == &Token::Question {
                let q_span = self.peek_span();
                self.advance()?;
                let span = Span::new(lhs.span.start, q_span.end);
                lhs = Expr::new(ExprKind::Try(Box::new(lhs)), span);
                continue;
            }

            // Postfix `.N` — tuple projection (same precedence as `?`).
            if self.peek() == &Token::Dot {
                self.advance()?;
                let idx_span = self.peek_span();
                let index = match self.peek().clone() {
                    Token::Int(n) if n >= 0 => n as usize,
                    other => return Err(CompileError::UnexpectedToken {
                        expected: "non-negative integer index after `.`".into(),
                        found: other.to_string(),
                        span: idx_span,
                    }),
                };
                self.advance()?;
                let span = Span::new(lhs.span.start, idx_span.end);
                lhs = Expr::new(ExprKind::Proj { base: Box::new(lhs), index }, span);
                continue;
            }

            // Two-token `not in` binary operator.
            if self.peek() == &Token::Not && self.peek2() == &Token::In {
                let (left_bp, right_bp) = infix_bp_not_in();
                if left_bp <= min_bp {
                    break;
                }
                let op_span = self.peek_span();
                self.advance()?;
                self.advance()?;
                let rhs = self.parse_expr(right_bp)?;
                lhs = make_binop(BinOp::NotIn, lhs, rhs, op_span);
                continue;
            }

            let Some((left_bp, right_bp, op)) = self.peek_infix_op() else {
                break;
            };
            if left_bp <= min_bp {
                break;
            }

            let op_span = self.peek_span();
            self.advance()?;
            let rhs = self.parse_expr(right_bp)?;
            lhs = make_binop(op, lhs, rhs, op_span);
        }

        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<Expr, CompileError> {
        let span = self.peek_span();
        match self.peek().clone() {
            Token::Minus => {
                self.advance()?;
                let expr = self.parse_expr(PREFIX_BP_NEG)?;
                let end = expr.span.end;
                Ok(Expr::new(
                    ExprKind::UnOp { op: UnOp::Neg, expr: Box::new(expr) },
                    Span::new(span.start, end),
                ))
            }
            Token::Not => {
                self.advance()?;
                let expr = self.parse_expr(PREFIX_BP_NOT)?;
                let end = expr.span.end;
                Ok(Expr::new(
                    ExprKind::UnOp { op: UnOp::Not, expr: Box::new(expr) },
                    Span::new(span.start, end),
                ))
            }
            Token::If => {
                self.advance()?;
                let cond = self.parse_expr(0)?;
                self.expect(&Token::Then)?;
                let then_expr = self.parse_expr(0)?;
                self.expect(&Token::Else)?;
                let else_expr = self.parse_expr(0)?;
                let end = else_expr.span.end;
                Ok(Expr::new(
                    ExprKind::If {
                        cond: Box::new(cond),
                        then_expr: Box::new(then_expr),
                        else_expr: Box::new(else_expr),
                    },
                    Span::new(span.start, end),
                ))
            }
            Token::Fail => {
                self.advance()?;
                if self.peek_starts_expr() {
                    let inner = self.parse_expr(0)?;
                    let end = inner.span.end;
                    Ok(Expr::new(ExprKind::FailWith(Box::new(inner)), Span::new(span.start, end)))
                } else {
                    Ok(Expr::new(ExprKind::FailLit, span))
                }
            }
            _ => self.parse_atom(),
        }
    }

    fn parse_atom(&mut self) -> Result<Expr, CompileError> {
        let span = self.peek_span();
        match self.peek().clone() {
            Token::Int(n) => {
                self.advance()?;
                Ok(Expr::new(ExprKind::IntLit(n), span))
            }
            Token::True => {
                self.advance()?;
                Ok(Expr::new(ExprKind::BoolLit(true), span))
            }
            Token::False => {
                self.advance()?;
                Ok(Expr::new(ExprKind::BoolLit(false), span))
            }
            Token::Ident(name) => {
                self.advance()?;
                if self.peek() == &Token::LParen {
                    self.parse_call(Symbol::new(name), span)
                } else {
                    Ok(Expr::new(ExprKind::Var(Symbol::new(name)), span))
                }
            }
            Token::LParen => {
                self.advance()?;
                let first = self.parse_expr(0)?;
                if self.peek() == &Token::Comma {
                    // Tuple literal: (e0, e1, …)
                    let mut elems = vec![first];
                    while self.peek() == &Token::Comma {
                        self.advance()?;
                        if self.peek() == &Token::RParen { break; }
                        elems.push(self.parse_expr(0)?);
                    }
                    let end_span = self.peek_span();
                    self.expect(&Token::RParen)?;
                    Ok(Expr::new(ExprKind::Tuple(elems), Span::new(span.start, end_span.end)))
                } else {
                    // Plain grouping: (expr)
                    let end_span = self.peek_span();
                    self.expect(&Token::RParen)?;
                    Ok(Expr::new(first.kind, Span::new(span.start, end_span.end)))
                }
            }
            Token::LBrace => {
                self.advance()?;
                self.skip_newlines()?;
                if self.peek() == &Token::RBrace {
                    let end_span = self.peek_span();
                    self.advance()?;
                    return Ok(Expr::new(ExprKind::SetLit(vec![]), Span::new(span.start, end_span.end)));
                }
                let first = self.parse_expr(0)?;
                self.skip_newlines()?;
                // One token of lookahead: `for` → comprehension, else set literal.
                if self.peek() == &Token::For {
                    self.advance()?;
                    let var = self.expect_ident()?;
                    self.expect(&Token::In)?;
                    let source = self.parse_set_expr()?;
                    self.skip_newlines()?;
                    let filter = if self.peek() == &Token::If {
                        self.advance()?;
                        let f = self.parse_expr(0)?;
                        self.skip_newlines()?;
                        Some(f)
                    } else {
                        None
                    };
                    let end_span = self.peek_span();
                    self.expect(&Token::RBrace)?;
                    return Ok(Expr::new(
                        ExprKind::Comprehension {
                            output: Box::new(first),
                            var,
                            source: Box::new(source),
                            filter: filter.map(Box::new),
                        },
                        Span::new(span.start, end_span.end),
                    ));
                }
                let mut elements = vec![first];
                while self.peek() == &Token::Comma {
                    self.advance()?;
                    self.skip_newlines()?;
                    if self.peek() == &Token::RBrace { break; } // trailing comma
                    elements.push(self.parse_expr(0)?);
                    self.skip_newlines()?;
                }
                let end_span = self.peek_span();
                self.expect(&Token::RBrace)?;
                Ok(Expr::new(ExprKind::SetLit(elements), Span::new(span.start, end_span.end)))
            }
            // Reserved built-in functions: always called with exactly one argument.
            Token::From => {
                self.advance()?;
                self.parse_call(Symbol::new("from"), span)
            }
            Token::Size => {
                self.advance()?;
                self.parse_call(Symbol::new("size"), span)
            }
            other => Err(CompileError::UnexpectedToken {
                expected: "expression".into(),
                found: other.to_string(),
                span,
            }),
        }
    }

    fn parse_call(&mut self, callee: Symbol, start_span: Span) -> Result<Expr, CompileError> {
        self.expect(&Token::LParen)?;
        let mut args = Vec::new();
        if self.peek() != &Token::RParen {
            args.push(self.parse_expr(0)?);
            while self.peek() == &Token::Comma {
                self.advance()?;
                args.push(self.parse_expr(0)?);
            }
        }
        let end_span = self.peek_span();
        self.expect(&Token::RParen)?;
        Ok(Expr::new(
            ExprKind::Call { callee, args },
            Span::new(start_span.start, end_span.end),
        ))
    }

    fn peek_infix_op(&self) -> Option<(u8, u8, BinOp)> {
        let (lbp, rbp, op) = match self.peek() {
            Token::Or       => (1,  2,  BinOp::Or),
            Token::And      => (3,  4,  BinOp::And),
            Token::EqEq     => (5,  6,  BinOp::Eq),
            Token::BangEq   => (5,  6,  BinOp::Ne),
            Token::Lt       => (5,  6,  BinOp::Lt),
            Token::LtEq     => (5,  6,  BinOp::Le),
            Token::Gt       => (5,  6,  BinOp::Gt),
            Token::GtEq     => (5,  6,  BinOp::Ge),
            Token::In       => (5,  6,  BinOp::In),
            // `!!` binds below `|` on the left (so `A | B !! C` = `(A | B) !! C`)
            // and at the same level on the right (so `A !! B | C` = `A !! (B | C)`).
            Token::BangBang => (6,  6,  BinOp::ErrorUnion),
            Token::Pipe     => (7,  8,  BinOp::Union),
            Token::Caret    => (9,  10, BinOp::SymDiff),
            Token::Amp      => (11, 12, BinOp::Intersect),
            Token::Plus     => (13, 14, BinOp::Add),
            Token::Minus    => (13, 14, BinOp::Sub),
            Token::Star     => (15, 16, BinOp::Mul),
            Token::Slash    => (15, 16, BinOp::Div),
            _ => return None,
        };
        Some((lbp, rbp, op))
    }

    /// Returns true when the current lookahead token could start an expression.
    ///
    /// Used to decide whether `fail` is a bare sentinel or has a payload.
    fn peek_starts_expr(&self) -> bool {
        matches!(
            self.peek(),
            Token::Int(_)
                | Token::True
                | Token::False
                | Token::Ident(_)
                | Token::Minus
                | Token::Not
                | Token::If
                | Token::LParen
                | Token::LBrace
        )
    }

    // ── Utilities ─────────────────────────────────────────────────────────────

    fn expect_ident(&mut self) -> Result<Symbol, CompileError> {
        let span = self.peek_span();
        let (tok, _) = self.advance()?;
        match tok {
            Token::Ident(name) => Ok(Symbol::new(name)),
            other => Err(CompileError::UnexpectedToken {
                expected: "identifier".into(),
                found: other.to_string(),
                span,
            }),
        }
    }

    // ── Convenience entry points ───────────────────────────────────────────────

    /// Parse a single expression followed by EOF (used in tests and REPL).
    pub fn parse_expr_eof(&mut self) -> Result<Expr, CompileError> {
        let expr = self.parse_expr(0)?;
        self.skip_newlines()?;
        if self.peek() != &Token::Eof {
            return Err(CompileError::UnexpectedToken {
                expected: "<eof>".into(),
                found: self.peek().to_string(),
                span: self.peek_span(),
            });
        }
        Ok(expr)
    }
}

// ── Binding powers ────────────────────────────────────────────────────────────

const PREFIX_BP_NOT: u8 = 4; // absorbs comparisons: `not x == y` → `not (x == y)`
const PREFIX_BP_NEG: u8 = 17; // tighter than `*`/`/`: `-x * y` → `(-x) * y`

fn infix_bp_not_in() -> (u8, u8) {
    (5, 6)
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn make_binop(op: BinOp, lhs: Expr, rhs: Expr, _op_span: Span) -> Expr {
    let span = Span::new(lhs.span.start, rhs.span.end);
    Expr::new(ExprKind::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }, span)
}

// ── Free-function wrappers ────────────────────────────────────────────────────

/// Parse `src` as a single expression followed by EOF.
pub fn parse_expr(src: &str) -> Result<Expr, CompileError> {
    Parser::new(src)?.parse_expr_eof()
}

/// Parse `src` as a complete source file.
pub fn parse_file(src: &str) -> Result<Vec<Item>, CompileError> {
    Parser::new(src)?.parse_file()
}
