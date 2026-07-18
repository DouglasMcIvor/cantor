//! Top-level item parsing: name defs, function signatures, and params —
//! plus the `X * N` repeated-product desugaring applied to every set expression.

use super::Parser;
use super::lexer::Token;

use crate::{
    ast::{
        BinOp, DefKind, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item, NameDef,
        Param,
    },
    error::CompileError,
    span::{Span, Symbol},
};

impl<'src> Parser<'src> {
    pub(super) fn parse_item(&mut self) -> Result<Item, CompileError> {
        // `equiv f, g` — top-level function-equivalence proof obligation.
        if self.peek() == &Token::Equiv {
            return self.parse_equiv_decl();
        }

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

    /// Parse `equiv f, g` — a top-level function-equivalence proof obligation.
    /// No new name is introduced; `lhs`/`rhs` are references to functions
    /// defined elsewhere (in either order relative to this declaration).
    fn parse_equiv_decl(&mut self) -> Result<Item, CompileError> {
        let start = self.peek_span();
        self.expect(&Token::Equiv)?;
        let lhs = self.expect_ident()?;
        self.expect(&Token::Comma)?;
        let rhs_span = self.peek_span();
        let rhs = self.expect_ident()?;
        Ok(Item::EquivDecl {
            lhs,
            rhs,
            span: Span::new(start.start, rhs_span.end),
        })
    }

    /// Parse an unannotated name def: `Name = [alias|distinct] expr`.
    ///
    /// Called when we see `Ident '='` at the top level (peeked two tokens ahead).
    fn parse_unannotated_name_def(&mut self) -> Result<Item, CompileError> {
        let start = self.peek_span();
        let name = self.expect_ident()?;
        self.expect(&Token::Eq)?;
        let kind = match self.peek().clone() {
            Token::Distinct => {
                self.advance()?;
                DefKind::Distinct
            }
            Token::Alias => {
                self.advance()?;
                DefKind::Alias
            }
            _ => DefKind::Alias,
        };
        let value = self.parse_set_expr()?;
        let end = value.span.end;
        Ok(Item::NameDef(NameDef {
            name,
            kind,
            ty: None,
            value,
            span: Span::new(start.start, end),
        }))
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
        Ok(FunctionSig {
            domain,
            range,
            span: Span::new(start.start, end),
        })
    }

    /// Parse a set expression in signature position.
    ///
    /// After parsing, `X * N` where N is a positive integer literal is desugared
    /// to `X * X * … * X` (N copies, left-associative) so that downstream passes
    /// (solver, codegen) never see an integer literal in the rhs of a product.
    pub(super) fn parse_set_expr(&mut self) -> Result<Expr, CompileError> {
        // We parse a full expression but Arrow is not an infix operator so the
        // Pratt loop will naturally stop before `->`; the `-` in `->` is consumed
        // by the lexer as Arrow, not Minus, so there's no ambiguity.
        let expr = self.parse_expr(0)?;
        Ok(desugar_repeated_product(expr))
    }

    // ── Parameters ────────────────────────────────────────────────────────────

    fn parse_params(&mut self) -> Result<Vec<Param>, CompileError> {
        let mut params = Vec::new();
        if self.peek() == &Token::RParen {
            return Ok(params);
        }
        params.push(self.parse_one_param(0)?);
        let mut index = 1;
        while self.peek() == &Token::Comma {
            self.advance()?;
            params.push(self.parse_one_param(index)?);
            index += 1;
        }
        Ok(params)
    }

    /// `index` is this parameter's position within its parameter list —
    /// used only to name the synthesized binder for a literal-arm param
    /// (`f(0) = ...`), so two literal params in one list don't collide.
    fn parse_one_param(&mut self, index: usize) -> Result<Param, CompileError> {
        let span = self.peek_span();
        if let Token::Int(n) = self.peek().clone() {
            // Literal-arm overloading sugar: `f(0) = ...` narrows this arm's
            // declared domain slice to `{0}`. Desugars to the same
            // synthesized-equality-guard shape as `x for x == 0` on a fresh
            // internal binder — reuses the guard machinery above rather
            // than a separate domain-restriction mechanism.
            self.advance()?;
            let name = Symbol::new(format!("__lit{index}"));
            let guard = Expr::new(
                ExprKind::BinOp {
                    op: BinOp::Eq,
                    lhs: Box::new(Expr::new(ExprKind::Var(name.clone()), span)),
                    rhs: Box::new(Expr::new(ExprKind::IntLit(n), span)),
                },
                span,
            );
            return Ok(Param {
                name,
                guard: Some(guard),
                span,
            });
        }
        let name = self.expect_ident()?;
        let guard = if self.peek() == &Token::For {
            self.advance()?;
            Some(self.parse_expr(0)?)
        } else {
            None
        };
        let end = guard.as_ref().map_or(span.end, |g| g.span.end);
        Ok(Param {
            name,
            guard,
            span: Span::new(span.start, end),
        })
    }
}

// ── Repeated-product desugaring ───────────────────────────────────────────────

/// Rewrite `lhs * N` (where N is a positive integer literal) to N copies of
/// `lhs` in a left-associative product: `((lhs * lhs) * lhs) * …`.
///
/// Applied recursively so that `(Int * 3) | Bool` correctly expands the inner
/// product.  Only called from `parse_set_expr` — in value position `x * 3`
/// means arithmetic multiplication and must not be rewritten.
fn desugar_repeated_product(expr: Expr) -> Expr {
    let span = expr.span;
    match expr.kind {
        ExprKind::BinOp {
            op: BinOp::Mul,
            lhs,
            rhs,
        } => {
            let lhs = desugar_repeated_product(*lhs);
            match rhs.kind {
                ExprKind::IntLit(1) => lhs,
                ExprKind::IntLit(n) if n >= 2 => {
                    let mut result = lhs.clone();
                    for _ in 1..n {
                        result = Expr::new(
                            ExprKind::BinOp {
                                op: BinOp::Mul,
                                lhs: Box::new(result),
                                rhs: Box::new(lhs.clone()),
                            },
                            span,
                        );
                    }
                    result
                }
                _ => {
                    let rhs = desugar_repeated_product(*rhs);
                    Expr::new(
                        ExprKind::BinOp {
                            op: BinOp::Mul,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        span,
                    )
                }
            }
        }
        ExprKind::BinOp { op, lhs, rhs } => {
            let lhs = desugar_repeated_product(*lhs);
            let rhs = desugar_repeated_product(*rhs);
            Expr::new(
                ExprKind::BinOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            )
        }
        // Recurse into the element-set of a Kleene star so `Int * 3 *` desugars
        // the inner `Int * 3` → `Int * Int * Int` before wrapping in KleeneStar.
        ExprKind::KleeneStar(inner) => {
            let inner = desugar_repeated_product(*inner);
            Expr::new(ExprKind::KleeneStar(Box::new(inner)), span)
        }
        _ => expr,
    }
}
