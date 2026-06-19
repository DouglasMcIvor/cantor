pub mod lexer;

use lexer::{Lexer, Token};

use crate::{
    ast::{BinOp, Expr, ExprKind, UnOp},
    error::CompileError,
    span::{Span, Symbol},
};

/// Recursive-descent / Pratt parser for Cantor expressions.
///
/// Two tokens of lookahead are maintained so that the two-token
/// binary operator `not in` can be recognised in infix position without
/// backtracking.
pub struct Parser<'src> {
    lexer: Lexer<'src>,
    peek0: (Token, Span), // next token to consume
    peek1: (Token, Span), // token after that
}

impl<'src> Parser<'src> {
    pub fn new(src: &'src str) -> Result<Self, CompileError> {
        let mut lexer = Lexer::new(src);
        let peek0 = lexer.next_token()?;
        let peek1 = lexer.next_token()?;
        Ok(Self { lexer, peek0, peek1 })
    }

    // ── Lookahead ────────────────────────────────────────────────────────────

    fn peek(&self) -> &Token {
        &self.peek0.0
    }

    fn peek_span(&self) -> Span {
        self.peek0.1
    }

    fn peek2(&self) -> &Token {
        &self.peek1.0
    }

    /// Consume and return the current lookahead token, then shift the buffer.
    fn advance(&mut self) -> Result<(Token, Span), CompileError> {
        let new_peek1 = self.lexer.next_token()?;
        let old_peek1 = std::mem::replace(&mut self.peek1, new_peek1);
        Ok(std::mem::replace(&mut self.peek0, old_peek1))
    }

    /// Consume the current token, asserting its kind for internal use.
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

    // ── Public entry point ───────────────────────────────────────────────────

    /// Parse a complete expression, then expect EOF.
    pub fn parse_expr_eof(&mut self) -> Result<Expr, CompileError> {
        let expr = self.parse_expr(0)?;
        if self.peek() != &Token::Eof {
            return Err(CompileError::UnexpectedToken {
                expected: "<eof>".into(),
                found: self.peek().to_string(),
                span: self.peek_span(),
            });
        }
        Ok(expr)
    }

    // ── Pratt core ───────────────────────────────────────────────────────────

    /// Parse an expression with at least the given minimum left-binding power.
    /// Corresponds to a single invocation in the standard Pratt algorithm.
    pub fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, CompileError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            // Check for the two-token `not in` binary operator first.
            if self.peek() == &Token::Not && self.peek2() == &Token::In {
                let (left_bp, right_bp) = infix_bp_not_in();
                if left_bp <= min_bp {
                    break;
                }
                let op_span = self.peek_span();
                self.advance()?; // consume `not`
                self.advance()?; // consume `in`
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

    /// Parse a prefix position: unary operators or an atom.
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
            _ => self.parse_atom(),
        }
    }

    /// Parse an atom: literal, identifier, call, or parenthesised expression.
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
                // A `(` immediately after an identifier means a function call.
                if self.peek() == &Token::LParen {
                    self.parse_call(Symbol::new(name), span)
                } else {
                    Ok(Expr::new(ExprKind::Var(Symbol::new(name)), span))
                }
            }
            Token::LParen => {
                self.advance()?;
                let expr = self.parse_expr(0)?;
                let end_span = self.peek_span();
                self.expect(&Token::RParen)?;
                // Preserve inner span but extend to closing paren.
                Ok(Expr::new(expr.kind, Span::new(span.start, end_span.end)))
            }
            Token::For | Token::If => {
                Err(CompileError::UnexpectedToken {
                    expected: "expression".into(),
                    found: format!("`{}` (comprehensions not yet implemented)", self.peek()),
                    span,
                })
            }
            other => Err(CompileError::UnexpectedToken {
                expected: "expression".into(),
                found: other.to_string(),
                span,
            }),
        }
    }

    /// Parse a function call `callee(arg, arg, …)`. The callee name and its
    /// span have already been consumed; we are positioned at `(`.
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

    /// Return `(left_bp, right_bp, op)` if the current token begins an infix
    /// operator, or `None` if it doesn't.
    fn peek_infix_op(&self) -> Option<(u8, u8, BinOp)> {
        let (lbp, rbp, op) = match self.peek() {
            Token::Or     => (1,  2,  BinOp::Or),
            Token::And    => (3,  4,  BinOp::And),
            Token::EqEq   => (5,  6,  BinOp::Eq),
            Token::BangEq => (5,  6,  BinOp::Ne),
            Token::Lt     => (5,  6,  BinOp::Lt),
            Token::LtEq   => (5,  6,  BinOp::Le),
            Token::Gt     => (5,  6,  BinOp::Gt),
            Token::GtEq   => (5,  6,  BinOp::Ge),
            Token::In     => (5,  6,  BinOp::In),
            Token::Pipe   => (7,  8,  BinOp::Union),
            Token::Caret  => (9,  10, BinOp::SymDiff),
            Token::Amp    => (11, 12, BinOp::Intersect),
            Token::Plus   => (13, 14, BinOp::Add),
            Token::Minus  => (13, 14, BinOp::Sub),
            Token::Star   => (15, 16, BinOp::Mul),
            Token::Slash  => (15, 16, BinOp::Div),
            _ => return None,
        };
        Some((lbp, rbp, op))
    }
}

// ── Binding powers ────────────────────────────────────────────────────────────

// `not` prefix: right_bp is just below comparison left_bp (5), so
// `not x == y` parses as `not (x == y)` rather than `(not x) == y`.
const PREFIX_BP_NOT: u8 = 4;

// Unary minus binds tighter than `*` and `/` (left_bp 15), so
// `-x * y` parses as `(-x) * y`.
const PREFIX_BP_NEG: u8 = 17;

fn infix_bp_not_in() -> (u8, u8) {
    (5, 6) // same level as other comparisons
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn make_binop(op: BinOp, lhs: Expr, rhs: Expr, _op_span: Span) -> Expr {
    let span = Span::new(lhs.span.start, rhs.span.end);
    Expr::new(ExprKind::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }, span)
}

// ── Convenience free function ─────────────────────────────────────────────────

/// Parse `src` as a single expression (followed by EOF). Convenience wrapper
/// for tests and the REPL-style driver.
pub fn parse_expr(src: &str) -> Result<Expr, CompileError> {
    Parser::new(src)?.parse_expr_eof()
}
