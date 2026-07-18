//! Pratt expression parsing: prefix/atom parsing, the infix precedence loop,
//! and the postfix `?`/`.N`/`[expr]`/Kleene-star operators.

use super::Parser;
use super::lexer::{StrPart, Token};

use crate::{
    ast::{BinOp, Expr, ExprKind, UnOp},
    error::CompileError,
    span::{Span, Symbol},
};

/// True when `tok` can legally begin an expression (used for Kleene-star disambiguation).
// Disambiguates postfix `*` (Kleene star) from binary `*` (Cartesian product /
// multiplication).  `-` is intentionally excluded: `X* - A` must parse as
// KleeneStar(X) Sub A (set difference), not as X Mul UnOp(Neg, A).
// Use `x * (-5)` instead of `x * -5` if you need to multiply by a literal negative.
fn token_starts_expr_after_star(tok: &Token) -> bool {
    matches!(
        tok,
        Token::Int(_)
            | Token::Char(_)
            | Token::Str(_)
            | Token::InterpStr(_)
            | Token::True
            | Token::False
            | Token::Ident(_)
            | Token::Not
            | Token::If
            | Token::LParen
            | Token::LBrace
            | Token::LBracket
            | Token::Fail
            | Token::NoneLit
            | Token::From
            | Token::Size
    )
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
    Expr::new(
        ExprKind::BinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        span,
    )
}

impl<'src> Parser<'src> {
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
                    other => {
                        return Err(CompileError::UnexpectedToken {
                            expected: "non-negative integer index after `.`".into(),
                            found: other.to_string(),
                            span: idx_span,
                        });
                    }
                };
                self.advance()?;
                let span = Span::new(lhs.span.start, idx_span.end);
                lhs = Expr::new(
                    ExprKind::Proj {
                        base: Box::new(lhs),
                        index,
                    },
                    span,
                );
                continue;
            }

            // Postfix `[expr]` — index operator.
            //   • Non-negative integer literal index → `Proj` (same as `x.N` dot notation)
            //   • Any other expression          → `Index` (runtime, for vectors X*)
            if self.peek() == &Token::LBracket {
                self.advance()?;
                // Peek: is the index a non-negative integer literal?
                if let Token::Int(n) = self.peek().clone()
                    && n >= 0
                {
                    let idx = n as usize;
                    self.advance()?;
                    let close_span = self.peek_span();
                    self.expect(&Token::RBracket)?;
                    let span = Span::new(lhs.span.start, close_span.end);
                    lhs = Expr::new(
                        ExprKind::Proj {
                            base: Box::new(lhs),
                            index: idx,
                        },
                        span,
                    );
                    continue;
                }
                // General expression index → runtime Index node (vectors only).
                let index_expr = self.parse_expr(0)?;
                let close_span = self.peek_span();
                self.expect(&Token::RBracket)?;
                let span = Span::new(lhs.span.start, close_span.end);
                lhs = Expr::new(
                    ExprKind::Index {
                        base: Box::new(lhs),
                        index: Box::new(index_expr),
                    },
                    span,
                );
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

            // `!!` desugars to `lhs | (Fail * rhs)` — same precedences as before:
            // lbp=6 so `A | B !! C` = `(A | B) !! C`, rbp=6 so `A !! B | C` = `A !! (B | C)`.
            if self.peek() == &Token::BangBang {
                if 6 <= min_bp {
                    break;
                }
                let op_span = self.peek_span();
                self.advance()?;
                let rhs = self.parse_expr(6)?;
                let fail_var = Expr::new(ExprKind::Var(Symbol::new("Fail")), op_span);
                let fail_product = make_binop(BinOp::Mul, fail_var, rhs, op_span);
                lhs = make_binop(BinOp::Union, lhs, fail_product, op_span);
                continue;
            }

            // Postfix `*` — Kleene star.
            // Disambiguation: `X * Y` (product/multiply) has an expression following `*`;
            // `X*` (Kleene star) has a non-expression token following `*` (e.g. `->`, `)`, newline).
            // We only produce KleeneStar when the token after `*` cannot start an expression.
            if self.peek() == &Token::Star && !token_starts_expr_after_star(self.peek2()) {
                let star_span = self.peek_span();
                self.advance()?;
                let span = Span::new(lhs.span.start, star_span.end);
                lhs = Expr::new(ExprKind::KleeneStar(Box::new(lhs)), span);
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
                    ExprKind::UnOp {
                        op: UnOp::Neg,
                        expr: Box::new(expr),
                    },
                    Span::new(span.start, end),
                ))
            }
            Token::Not => {
                self.advance()?;
                let expr = self.parse_expr(PREFIX_BP_NOT)?;
                let end = expr.span.end;
                Ok(Expr::new(
                    ExprKind::UnOp {
                        op: UnOp::Not,
                        expr: Box::new(expr),
                    },
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
                    Ok(Expr::new(
                        ExprKind::FailWith(Box::new(inner)),
                        Span::new(span.start, end),
                    ))
                } else {
                    Ok(Expr::new(ExprKind::FailLit, span))
                }
            }
            // `none` is deliberately bare-only — no `none expr` payload form
            // (unlike `fail`/`fail expr`), so it never consumes a following
            // expression the way `Token::Fail` does above.
            Token::NoneLit => {
                self.advance()?;
                Ok(Expr::new(ExprKind::NoneLit, span))
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
            Token::Char(c) => {
                self.advance()?;
                Ok(Expr::new(ExprKind::CharLit(c), span))
            }
            Token::Str(s) => {
                self.advance()?;
                // Desugars to a `Tuple` of `CharLit`s — see `Expr::string_lit`.
                // Built inline (not via that helper) so every element gets
                // the whole string token's span rather than `Span::dummy()`.
                let elems = s
                    .chars()
                    .map(|c| Expr::new(ExprKind::CharLit(c), span))
                    .collect();
                Ok(Expr::new(ExprKind::Tuple(elems), span))
            }
            Token::InterpStr(parts) => {
                self.advance()?;
                desugar_interp_parts(parts, span)
            }
            Token::Ident(name) => {
                self.advance()?;
                // `Name.Label(...)` — named-union-arm constructor call
                // (`Shape.Circle(3)`). `.` followed by an identifier is
                // otherwise unused syntax today (`.N` tuple projection,
                // handled by the postfix loop in `parse_expr`, requires an
                // integer), so this can't shadow any existing valid program.
                // Combined into one synthesized `Symbol` (e.g. "Shape.Circle")
                // and resolved structurally at elaboration/solver/codegen
                // time — no new `ExprKind`, reuses the ordinary `Call` path.
                if self.peek() == &Token::Dot && matches!(self.peek2(), Token::Ident(_)) {
                    self.advance()?; // consume `.`
                    let label = self.expect_ident()?;
                    let combined = Symbol::new(format!("{name}.{}", label.0));
                    return if self.peek() == &Token::LParen {
                        self.parse_call(combined, span)
                    } else {
                        Ok(Expr::new(ExprKind::Var(combined), span))
                    };
                }
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
                        if self.peek() == &Token::RParen {
                            break;
                        }
                        elems.push(self.parse_expr(0)?);
                    }
                    let end_span = self.peek_span();
                    self.expect(&Token::RParen)?;
                    Ok(Expr::new(
                        ExprKind::Tuple(elems),
                        Span::new(span.start, end_span.end),
                    ))
                } else {
                    // Plain grouping: (expr)
                    let end_span = self.peek_span();
                    self.expect(&Token::RParen)?;
                    Ok(Expr::new(first.kind, Span::new(span.start, end_span.end)))
                }
            }
            Token::LBracket => {
                // `[a, b, c]` — homogeneous array literal, desugars to Tuple.
                // TODO: enforce homogeneity (all elements in the same set X) once
                // range inference is available; for now it is identical to `(a, b, c)`.
                self.advance()?;
                if self.peek() == &Token::RBracket {
                    let end_span = self.peek_span();
                    self.advance()?;
                    return Ok(Expr::new(
                        ExprKind::Tuple(vec![]),
                        Span::new(span.start, end_span.end),
                    ));
                }
                let first = self.parse_expr(0)?;
                let mut elems = vec![first];
                while self.peek() == &Token::Comma {
                    self.advance()?;
                    if self.peek() == &Token::RBracket {
                        break;
                    }
                    elems.push(self.parse_expr(0)?);
                }
                let end_span = self.peek_span();
                self.expect(&Token::RBracket)?;
                Ok(Expr::new(
                    ExprKind::Tuple(elems),
                    Span::new(span.start, end_span.end),
                ))
            }
            Token::LBrace => {
                self.advance()?;
                self.skip_newlines()?;
                if self.peek() == &Token::RBrace {
                    let end_span = self.peek_span();
                    self.advance()?;
                    return Ok(Expr::new(
                        ExprKind::SetLit(vec![]),
                        Span::new(span.start, end_span.end),
                    ));
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
                    if self.peek() == &Token::RBrace {
                        break;
                    } // trailing comma
                    elements.push(self.parse_expr(0)?);
                    self.skip_newlines()?;
                }
                let end_span = self.peek_span();
                self.expect(&Token::RBrace)?;
                Ok(Expr::new(
                    ExprKind::SetLit(elements),
                    Span::new(span.start, end_span.end),
                ))
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
            Token::Or => (1, 2, BinOp::Or),
            Token::And => (3, 4, BinOp::And),
            Token::EqEq => (5, 6, BinOp::Eq),
            Token::BangEq => (5, 6, BinOp::Ne),
            Token::Lt => (5, 6, BinOp::Lt),
            Token::LtEq => (5, 6, BinOp::Le),
            Token::Gt => (5, 6, BinOp::Gt),
            Token::GtEq => (5, 6, BinOp::Ge),
            Token::In => (5, 6, BinOp::In),
            Token::Pipe => (7, 8, BinOp::Union),
            Token::Caret => (9, 10, BinOp::SymDiff),
            Token::Amp => (11, 12, BinOp::Intersect),
            Token::Plus => (13, 14, BinOp::Add),
            Token::Minus => (13, 14, BinOp::Sub),
            Token::PlusPlus => (13, 14, BinOp::Concat),
            Token::Star => (15, 16, BinOp::Mul),
            Token::Slash => (15, 16, BinOp::Div),
            Token::Rem => (15, 16, BinOp::Rem),
            Token::Quot => (15, 16, BinOp::Quot),
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
                | Token::Char(_)
                | Token::Str(_)
                | Token::InterpStr(_)
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

/// Desugars an interpolated string's parts (`Token::InterpStr`, produced by
/// `Lexer::scan_string_literal`) into a left-associated `++` chain over
/// literal-chunk `Tuple`s and `show(...)` calls — e.g. `"n={x}!"` becomes
/// `('n', '=') ++ show(x) ++ ('!')`, reusing the exact `Tuple`-of-`CharLit`
/// shape `Expr::string_lit`/plain `Token::Str` already produces so every
/// piece coerces to `Vector(Char)` via existing machinery, no new solver/
/// codegen support needed for the string parts themselves. Each `{expr}`
/// chunk is parsed independently (`super::parse_expr`, the same free
/// function `Parser::new` + `parse_expr_eof` wraps) via a fresh `Lexer`/
/// `Parser` over its own raw source text, then `Expr::shift_spans`/
/// `CompileError::shift_span` move every resulting span from "offset 0
/// within the extracted substring" to its real position in the original
/// file — so a mistake inside `{...}` still points at the right column.
fn desugar_interp_parts(parts: Vec<StrPart>, token_span: Span) -> Result<Expr, CompileError> {
    let mut pieces: Vec<Expr> = Vec::new();
    for part in parts {
        match part {
            StrPart::Lit(s) => {
                // Empty chunks (e.g. the leading/trailing `Lit` around a
                // string that starts/ends with `{...}`, or between two
                // adjacent `{...}{...}` chunks) are omitted rather than
                // contributing an empty `Tuple(vec![])` — an empty tuple
                // doesn't coerce cleanly to `Vector` (`kind::merge_concat_kinds`
                // needs a non-empty tuple on at least one side to borrow an
                // element Kind from).
                if s.is_empty() {
                    continue;
                }
                let elems = s
                    .chars()
                    .map(|c| Expr::new(ExprKind::CharLit(c), token_span))
                    .collect();
                pieces.push(Expr::new(ExprKind::Tuple(elems), token_span));
            }
            StrPart::Expr(raw, chunk_span) => {
                let mut expr =
                    super::parse_expr(&raw).map_err(|e| e.shift_span(chunk_span.start))?;
                expr.shift_spans(chunk_span.start);
                pieces.push(Expr::new(
                    ExprKind::Call {
                        callee: Symbol::new("show"),
                        args: vec![expr],
                    },
                    chunk_span,
                ));
            }
        }
    }
    // `interpolated` (the flag guarding `Token::InterpStr` vs plain
    // `Token::Str`) is only ever set once at least one `{expr}` chunk was
    // scanned, so `pieces` always has at least one element here.
    let mut iter = pieces.into_iter();
    let first = iter
        .next()
        .expect("interpolated string must have at least one {expr} chunk");
    Ok(iter.fold(first, |acc, next| {
        Expr::new(
            ExprKind::BinOp {
                op: BinOp::Concat,
                lhs: Box::new(acc),
                rhs: Box::new(next),
            },
            token_span,
        )
    }))
}
