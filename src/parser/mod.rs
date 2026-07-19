pub mod lexer;

mod expr;
mod items;
mod stmt;

use lexer::{Lexer, Token};

use crate::{ast::Item, error::CompileError, span::Span, span::Symbol};

/// Recursive-descent / Pratt parser for Cantor.
///
/// Two tokens of lookahead so that `not in` (two-token infix operator) and
/// `ident =` (assignment statement) can be recognised without backtracking.
pub struct Parser<'src> {
    lexer: Lexer<'src>,
    peek0: (Token, Span),
    peek1: (Token, Span),
    /// Fresh-id counter for `ast::FunctionDef::ordered_group` — bumped once
    /// per ordered guard group parsed, never reused, so two groups (even of
    /// the same name) never collide.
    next_ordered_group_id: u32,
}

impl<'src> Parser<'src> {
    pub fn new(src: &'src str) -> Result<Self, CompileError> {
        let mut lexer = Lexer::new(src);
        let peek0 = lexer.next_token()?;
        let peek1 = lexer.next_token()?;
        Ok(Self {
            lexer,
            peek0,
            peek1,
            next_ordered_group_id: 0,
        })
    }

    /// Allocate a fresh id for a new ordered guard group — see
    /// `ast::FunctionDef::ordered_group`.
    pub(super) fn fresh_ordered_group_id(&mut self) -> u32 {
        let id = self.next_ordered_group_id;
        self.next_ordered_group_id += 1;
        id
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

    // ── Top-level file ────────────────────────────────────────────────────────

    /// Parse a whole source file as a sequence of top-level items.
    pub fn parse_file(&mut self) -> Result<Vec<Item>, CompileError> {
        let mut items = Vec::new();
        self.skip_newlines()?;
        while self.peek() != &Token::Eof {
            items.extend(self.parse_item()?);
            self.skip_newlines()?;
        }
        Ok(items)
    }
}

// ── Free-function wrappers ────────────────────────────────────────────────────

/// Parse `src` as a single expression followed by EOF.
pub fn parse_expr(src: &str) -> Result<crate::ast::Expr, CompileError> {
    Parser::new(src)?.parse_expr_eof()
}

/// Parse `src` as a set expression (applying `X * N` repeated-product desugaring).
pub fn parse_set_expr(src: &str) -> Result<crate::ast::Expr, CompileError> {
    let mut p = Parser::new(src)?;
    let expr = p.parse_set_expr()?;
    p.skip_newlines()?;
    if p.peek() != &Token::Eof {
        return Err(CompileError::UnexpectedToken {
            expected: "<eof>".into(),
            found: p.peek().to_string(),
            span: p.peek_span(),
        });
    }
    Ok(expr)
}

/// Parse `src` as a complete source file.
pub fn parse_file(src: &str) -> Result<Vec<Item>, CompileError> {
    Parser::new(src)?.parse_file()
}
