//! Top-level item parsing: name defs, function signatures, and params —
//! plus the `X * N` repeated-product desugaring applied to every set expression.

use super::Parser;
use super::lexer::Token;

use crate::{
    ast::{
        BinOp, CtorPattern, DefKind, Expr, ExprKind, FunctionBody, FunctionDef, FunctionSig, Item,
        NameDef, Param,
    },
    error::CompileError,
    span::{Span, Symbol},
};

impl<'src> Parser<'src> {
    /// Parse one top-level item — almost always exactly one `Item`, except
    /// an ordered guard group (see `FunctionDef::ordered_group`), which
    /// produces one `Item::FunctionDef` per arm from a single leading
    /// signature.
    pub(super) fn parse_item(&mut self) -> Result<Vec<Item>, CompileError> {
        // `equiv f, g` — top-level function-equivalence proof obligation.
        if self.peek() == &Token::Equiv {
            return Ok(vec![self.parse_equiv_decl()?]);
        }

        // Unannotated name def: `Name = [alias|distinct] expr`
        // Disambiguated from annotated defs and functions (which have `:` after the name)
        // by checking the second lookahead token.
        if matches!(self.peek(), Token::Ident(_)) && self.peek2() == &Token::Eq {
            return Ok(vec![self.parse_unannotated_name_def()?]);
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
                return Ok(vec![Item::NameDef(NameDef {
                    name,
                    kind: DefKind::Alias,
                    ty: Some(first_expr),
                    value,
                    labels: None,
                    span: Span::new(start_span.start, end),
                })]);
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
        let (params, body, body_end) = self.parse_function_impl()?;
        let mut arms = vec![FunctionDef {
            name: name.clone(),
            sigs: sigs.clone(),
            params,
            body,
            ordered_group: None,
            span: Span::new(start_span.start, body_end),
        }];

        // Ordered guard group: a signature followed directly by 2+ bodies
        // with *no* repeated signature line between them (as opposed to the
        // sig-collection loop above, which already consumed any repeated
        // `name : ...` lines before we ever got here). Each continuation
        // arm is `name(` with no `:` — that's what tells it apart from a
        // fresh, ordinarily-disjoint overload, which always restates its
        // own signature first.
        loop {
            self.skip_newlines()?;
            if !(self.peek() == &Token::Ident(name.0.clone()) && self.peek2() == &Token::LParen) {
                break;
            }
            let arm_start = self.peek_span();
            self.advance()?; // consume repeated name
            let (params, body, body_end) = self.parse_function_impl()?;
            arms.push(FunctionDef {
                name: name.clone(),
                sigs: sigs.clone(),
                params,
                body,
                ordered_group: None,
                span: Span::new(arm_start.start, body_end),
            });
        }

        if arms.len() > 1 {
            let arity = arms[0].params.len();
            for arm in &arms {
                if arm.params.len() != arity {
                    return Err(CompileError::OrderedGroupArityMismatch {
                        name: name.0.clone(),
                        span: arm.span,
                    });
                }
                for p in &arm.params {
                    if p.guard.is_none() && p.ctor_pattern.is_none() && !p.is_wildcard {
                        return Err(CompileError::OrderedGroupBareParam {
                            name: name.0.clone(),
                            span: p.span,
                        });
                    }
                }
            }
            let group_id = self.fresh_ordered_group_id();
            for arm in &mut arms {
                arm.ordered_group = Some(group_id);
            }
        }

        Ok(arms.into_iter().map(Item::FunctionDef).collect())
    }

    /// Parse `(params) = expr` / `(params) { stmts }` — the implementation
    /// tail shared by an ordered guard group's first arm and every
    /// continuation arm (`parse_item`).
    fn parse_function_impl(&mut self) -> Result<(Vec<Param>, FunctionBody, u32), CompileError> {
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

        Ok((params, body, end))
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
        let (value, labels) = if kind == DefKind::Distinct {
            self.parse_distinct_value()?
        } else {
            (self.parse_set_expr()?, None)
        };
        let end = value.span.end;
        Ok(Item::NameDef(NameDef {
            name,
            kind,
            ty: None,
            value,
            labels,
            span: Span::new(start.start, end),
        }))
    }

    /// Parse the value of a `Name = distinct <value>` definition.
    ///
    /// Recognizes one extra form beyond the ordinary set expression
    /// `parse_set_expr` already handles: labeled union arms,
    /// `distinct (Label1: Expr1 | Label2: Expr2 | ...)`, each arm becoming an
    /// auto-generated constructor (`Name.Label1`, `Name.Label2`, …) —
    /// see `solver::encode_call`'s named-union-arm constructor block and
    /// `codegen::expr_call`'s matching tagged-struct constructor. The
    /// labeled arms fold into a `+`-joined (disjoint union) value, *not* a
    /// `|`-joined one, regardless of which separator token appears between
    /// labels in source — `+` is what forces a real runtime tag even when
    /// two arms share a Kind (`kind.rs`'s `BinOp::Add` arm never dedups,
    /// unlike `|`'s `union_if_distinct`), which is required for labels to
    /// mean anything: `Shape.Circle(3)` and `Shape.Radius(3)` must be
    /// provably distinct values even when both arms are plain `Nat`/`NatPos`
    /// (both `Kind::Int`). See `solver::sort::set_sort`'s
    /// `Union | DisjointUnion` arm, which forces the cross-kind DT path for
    /// any `DisjointUnion` regardless of whether the arm sorts happen to
    /// match.
    fn parse_distinct_value(&mut self) -> Result<(Expr, Option<Vec<Symbol>>), CompileError> {
        if self.peek() != &Token::LParen {
            return Ok((self.parse_set_expr()?, None));
        }
        let start = self.peek_span();
        self.advance()?; // consume `(`
        if !(matches!(self.peek(), Token::Ident(_)) && self.peek2() == &Token::Colon) {
            // Ordinary parenthesized set expression, e.g. `distinct (Meter * Meter)`.
            let inner = self.parse_expr(0)?;
            self.expect(&Token::RParen)?;
            return Ok((inner, None));
        }
        let mut labels = Vec::new();
        let mut arms = Vec::new();
        loop {
            let label = self.expect_ident()?;
            self.expect(&Token::Colon)?;
            // min_bp 8 stops the arm expression right before a following `|`
            // arm separator (lbp 7, see `peek_infix_op`) instead of
            // swallowing it as an ordinary union operator — still binds
            // tighter operators like `*`/`+`/`&` (all higher lbp) normally,
            // so `Rect: Nat * Nat` still parses `Nat * Nat` as one arm.
            let arm = self.parse_expr(8)?;
            labels.push(label);
            arms.push(arm);
            if self.peek() == &Token::Pipe {
                self.advance()?;
                continue;
            }
            break;
        }
        let end = self.peek_span();
        self.expect(&Token::RParen)?;
        let mut arm_iter = arms.into_iter();
        let first_arm = arm_iter
            .next()
            .expect("at least one `label: expr` pair — guarded by the Ident+Colon lookahead above");
        // Fold via `+` (disjoint union), not `|`: `+` is the operator that
        // already means "always force a runtime tag, even when arms share a
        // Kind" (`kind.rs`'s `BinOp::Add` arm never dedups). Labels are only
        // meaningful if every arm is genuinely distinguishable at runtime —
        // folding via `|` would silently let same-Kind labeled arms collapse
        // to one untagged value (`Shape.Circle(3)` and `Shape.Radius(3)`
        // becoming literally identical), which defeats the entire point of
        // giving arms separate labels/constructors in the first place.
        let value = arm_iter.fold(first_arm, |acc, next| {
            let span = Span::new(acc.span.start, next.span.end);
            Expr::new(
                ExprKind::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(acc),
                    rhs: Box::new(next),
                },
                span,
            )
        });
        let value = Expr::new(value.kind, Span::new(start.start, end.end));
        Ok((value, Some(labels)))
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
    /// (`f(0) = ...`) or a constructor-pattern param
    /// (`f(Tree.leaf2(x, y)) = ...`), so two such params in one list don't
    /// collide.
    fn parse_one_param(&mut self, index: usize) -> Result<Param, CompileError> {
        let span = self.peek_span();
        if self.peek() == &Token::Underscore {
            // Wildcard pattern (ordered guard groups only, enforced at
            // group-validation time in `parse_item`, not here — a bare `_`
            // is syntactically fine standalone, same as any other param
            // form, and rejecting it outside a group needs the group
            // context this function doesn't have). Matches unconditionally,
            // introduces no binder — the synthesized name is never
            // referenced.
            self.advance()?;
            return Ok(Param {
                name: Symbol::new(format!("__wild{index}")),
                guard: None,
                ctor_pattern: None,
                is_wildcard: true,
                span,
            });
        }
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
                ctor_pattern: None,
                is_wildcard: false,
                span,
            });
        }
        let name = self.expect_ident()?;
        // Constructor pattern: `Name.Label(x, ...)` (pattern-matching plan
        // step 4/4). A bare param is just an identifier with nothing after
        // it, so `.` right after one is unambiguous — same reasoning
        // `parser::expr`'s `Name.Label(...)` call-syntax comment relies on.
        if self.peek() == &Token::Dot {
            self.advance()?; // consume `.`
            let label = self.expect_ident()?;
            self.expect(&Token::LParen)?;
            let mut binders = vec![self.expect_ident()?];
            while self.peek() == &Token::Comma {
                self.advance()?;
                binders.push(self.expect_ident()?);
            }
            let end = self.peek_span();
            self.expect(&Token::RParen)?;
            return Ok(Param {
                name: Symbol::new(format!("__pat{index}")),
                guard: None,
                ctor_pattern: Some(CtorPattern {
                    union_name: name,
                    label,
                    binders,
                }),
                is_wildcard: false,
                span: Span::new(span.start, end.end),
            });
        }
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
            ctor_pattern: None,
            is_wildcard: false,
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
