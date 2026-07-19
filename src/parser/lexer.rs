use std::fmt;

use crate::{error::CompileError, span::Span};

/// A single lexical token.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    Int(i64),
    Char(char),
    Str(String),
    /// `"a{expr}b"` — an interpolated string with at least one `{expr}`
    /// chunk. A plain string with no unescaped `{` still lexes as the
    /// simpler `Token::Str` above; this variant only appears once
    /// interpolation is actually present, so no other token/parser code
    /// needs to change for the (overwhelmingly common) non-interpolated
    /// case. Desugared into a `++`/`show(...)` chain in `parser::expr`.
    InterpStr(Vec<StrPart>),

    // Keywords — expressions
    True,
    False,
    Not,
    And,
    Or,
    In,
    Rem,
    Quot,
    If,
    Then,
    Else,
    // Keywords — definitions / statements
    Mut,
    Assert,
    Assume,
    Require,
    Return,
    // Set definitions
    Alias,
    Distinct,
    // `equiv f, g` — top-level function-equivalence proof obligation
    Equiv,
    // Loops
    While,
    // Reserved for comprehensions (parser rejects with a "not yet" error)
    For,
    // Failure
    Fail,
    // Absence — the `None` singleton, mirrors `Fail` but carries no payload.
    NoneLit,
    // Built-in functions (reserved — cannot be shadowed by user definitions)
    From,
    Size,
    // `_` — wildcard parameter pattern (ordered guard groups only).
    Underscore,

    // Identifiers
    Ident(String),

    // Arithmetic / set-difference
    Plus,     // +
    PlusPlus, // ++ (vector concatenation)
    Minus,    // -  (also set difference; disambiguation is semantic)
    Star,     // *  (also Cartesian product in signature position)
    Slash,    // /

    // Set operators
    Pipe,     // |  union
    BangBang, // !! error-union (success | (Fail * error))
    Caret,    // ^  symmetric difference
    Amp,      // &  intersection

    // Comparison
    EqEq,   // ==
    BangEq, // !=
    Lt,     // <
    LtEq,   // <=
    Gt,     // >
    GtEq,   // >=

    // Definition / assignment
    Eq,      // =   (initial binding, pure-body connector)
    ColonEq, // :=  (reassignment of a `mut` variable)
    Arrow,   // ->  (signature range separator)
    Colon,   // :   (signature type separator)

    // Punctuation
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
    Comma,    // ,
    Question, // ?  (postfix propagate-failure operator)
    Dot,      // .  (tuple projection `t.0`)

    Newline, // \n at paren-depth 0 (statement terminator)
    Eof,
}

/// One chunk of an interpolated string, produced by the lexer's
/// brace-depth-aware scan (`Lexer::scan_string_literal`).
#[derive(Debug, Clone, PartialEq)]
pub enum StrPart {
    /// Literal text between/around `{...}` chunks, escapes already decoded.
    Lit(String),
    /// The raw, not-yet-parsed source text of one `{expr}` chunk (braces
    /// excluded) plus its span within the *original* source file — the
    /// parser re-lexes/re-parses this text with a fresh `Parser` and shifts
    /// the resulting spans by `span.start` so error messages still point at
    /// the right place in the original file.
    Expr(String, Span),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Int(n) => write!(f, "{n}"),
            Token::Char(c) => write!(f, "{c:?}"),
            Token::Str(s) => write!(f, "{s:?}"),
            Token::InterpStr(_) => f.write_str("interpolated string"),
            Token::Ident(s) => write!(f, "`{s}`"),
            Token::True => f.write_str("true"),
            Token::False => f.write_str("false"),
            Token::Not => f.write_str("not"),
            Token::And => f.write_str("and"),
            Token::Or => f.write_str("or"),
            Token::In => f.write_str("in"),
            Token::Rem => f.write_str("rem"),
            Token::Quot => f.write_str("quot"),
            Token::If => f.write_str("if"),
            Token::Then => f.write_str("then"),
            Token::Else => f.write_str("else"),
            Token::Mut => f.write_str("mut"),
            Token::Assert => f.write_str("assert"),
            Token::Assume => f.write_str("assume"),
            Token::Require => f.write_str("require"),
            Token::Return => f.write_str("return"),
            Token::Alias => f.write_str("alias"),
            Token::Distinct => f.write_str("distinct"),
            Token::Equiv => f.write_str("equiv"),
            Token::While => f.write_str("while"),
            Token::For => f.write_str("for"),
            Token::Fail => f.write_str("fail"),
            Token::NoneLit => f.write_str("none"),
            Token::From => f.write_str("from"),
            Token::Size => f.write_str("size"),
            Token::Underscore => f.write_str("_"),
            Token::Plus => f.write_str("+"),
            Token::PlusPlus => f.write_str("++"),
            Token::Minus => f.write_str("-"),
            Token::Star => f.write_str("*"),
            Token::Slash => f.write_str("/"),
            Token::Pipe => f.write_str("|"),
            Token::BangBang => f.write_str("!!"),
            Token::Caret => f.write_str("^"),
            Token::Amp => f.write_str("&"),
            Token::EqEq => f.write_str("=="),
            Token::BangEq => f.write_str("!="),
            Token::Lt => f.write_str("<"),
            Token::LtEq => f.write_str("<="),
            Token::Gt => f.write_str(">"),
            Token::GtEq => f.write_str(">="),
            Token::Eq => f.write_str("="),
            Token::ColonEq => f.write_str(":="),
            Token::Arrow => f.write_str("->"),
            Token::Colon => f.write_str(":"),
            Token::LParen => f.write_str("("),
            Token::RParen => f.write_str(")"),
            Token::LBrace => f.write_str("{"),
            Token::RBrace => f.write_str("}"),
            Token::LBracket => f.write_str("["),
            Token::RBracket => f.write_str("]"),
            Token::Comma => f.write_str(","),
            Token::Question => f.write_str("?"),
            Token::Dot => f.write_str("."),
            Token::Newline => f.write_str("<newline>"),
            Token::Eof => f.write_str("<eof>"),
        }
    }
}

/// Stateful lexer. Call `next_token()` repeatedly until `Token::Eof`.
pub struct Lexer<'src> {
    src: &'src str,
    pos: usize,
    /// Nesting depth of `(` and `)`. At depth > 0 newlines are suppressed.
    paren_depth: usize,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str) -> Self {
        Self {
            src,
            pos: 0,
            paren_depth: 0,
        }
    }

    fn peek_char(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn advance_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn skip_whitespace(&mut self) {
        while matches!(self.peek_char(), Some(' ' | '\t' | '\r')) {
            self.advance_char();
        }
    }

    fn scan_int(&mut self, start: usize) -> Result<(Token, Span), CompileError> {
        while matches!(self.peek_char(), Some(c) if c.is_ascii_digit()) {
            self.advance_char();
        }
        let text = &self.src[start..self.pos];
        let n = text
            .parse::<i64>()
            .map_err(|_| CompileError::InvalidIntLiteral {
                text: text.to_owned(),
                span: Span::new(start as u32, self.pos as u32),
            })?;
        Ok((Token::Int(n), Span::new(start as u32, self.pos as u32)))
    }

    /// Decode one escape sequence, having already consumed the leading `\`.
    /// `escape_start` is the position of the `\` itself, used for error spans.
    fn scan_escape(&mut self, escape_start: usize) -> Result<char, CompileError> {
        let Some(c) = self.advance_char() else {
            return Err(CompileError::InvalidEscape {
                found: "\\".to_owned(),
                span: Span::new(escape_start as u32, self.pos as u32),
            });
        };
        match c {
            'n' => Ok('\n'),
            't' => Ok('\t'),
            'r' => Ok('\r'),
            '0' => Ok('\0'),
            '\\' => Ok('\\'),
            '\'' => Ok('\''),
            '"' => Ok('"'),
            'u' => self.scan_unicode_escape(escape_start),
            other => Err(CompileError::InvalidEscape {
                found: format!("\\{other}"),
                span: Span::new(escape_start as u32, self.pos as u32),
            }),
        }
    }

    /// `\u{1F600}` — already consumed `\u`; expects `{`, 1-6 hex digits, `}`.
    fn scan_unicode_escape(&mut self, escape_start: usize) -> Result<char, CompileError> {
        let fail = |reason: &str, end: usize| CompileError::InvalidUnicodeEscape {
            reason: reason.to_owned(),
            span: Span::new(escape_start as u32, end as u32),
        };
        if self.peek_char() != Some('{') {
            return Err(fail("expected `{` after `\\u`", self.pos));
        }
        self.advance_char();
        let digits_start = self.pos;
        while matches!(self.peek_char(), Some(c) if c.is_ascii_hexdigit()) {
            self.advance_char();
        }
        let digits = &self.src[digits_start..self.pos];
        if digits.is_empty() {
            return Err(fail(
                "expected at least one hex digit inside `\\u{...}`",
                self.pos,
            ));
        }
        if self.peek_char() != Some('}') {
            return Err(fail("expected closing `}` after hex digits", self.pos));
        }
        self.advance_char();
        let cp = u32::from_str_radix(digits, 16)
            .map_err(|_| fail("hex digits do not fit in a u32", self.pos))?;
        char::from_u32(cp).ok_or_else(|| {
            fail(
                "not a valid Unicode scalar value (out of range or a surrogate)",
                self.pos,
            )
        })
    }

    fn scan_char_literal(&mut self, start: usize) -> Result<(Token, Span), CompileError> {
        let ch = match self.peek_char() {
            None | Some('\n') => {
                return Err(CompileError::UnterminatedLiteral {
                    quote: '\'',
                    span: Span::new(start as u32, self.pos as u32),
                });
            }
            Some('\'') => {
                return Err(CompileError::InvalidCharLiteral {
                    reason: "empty char literal".to_owned(),
                    span: Span::new(start as u32, self.pos as u32 + 1),
                });
            }
            Some('\\') => {
                let escape_start = self.pos;
                self.advance_char();
                self.scan_escape(escape_start)?
            }
            Some(c) => {
                self.advance_char();
                c
            }
        };
        match self.peek_char() {
            Some('\'') => {
                self.advance_char();
                Ok((Token::Char(ch), Span::new(start as u32, self.pos as u32)))
            }
            None | Some('\n') => Err(CompileError::UnterminatedLiteral {
                quote: '\'',
                span: Span::new(start as u32, self.pos as u32),
            }),
            Some(_) => {
                // More than one scalar value before the closing quote.
                while !matches!(self.peek_char(), Some('\'' | '\n') | None) {
                    self.advance_char();
                }
                let has_close = self.peek_char() == Some('\'');
                if has_close {
                    self.advance_char();
                }
                Err(CompileError::InvalidCharLiteral {
                    reason: "must contain exactly one character".to_owned(),
                    span: Span::new(start as u32, self.pos as u32),
                })
            }
        }
    }

    /// Scans `"..."`, splitting on unescaped `{expr}` chunks into
    /// interpolation parts. `{{`/`}}` are the escapes for a literal
    /// `{`/`}`. A string with no unescaped `{` at all still produces the
    /// plain `Token::Str` (zero behaviour change for the non-interpolated
    /// case, which is the overwhelming majority of string literals).
    fn scan_string_literal(&mut self, start: usize) -> Result<(Token, Span), CompileError> {
        let mut parts: Vec<StrPart> = Vec::new();
        let mut lit = String::new();
        let mut interpolated = false;
        loop {
            match self.peek_char() {
                None | Some('\n') => {
                    return Err(CompileError::UnterminatedLiteral {
                        quote: '"',
                        span: Span::new(start as u32, self.pos as u32),
                    });
                }
                Some('"') => {
                    self.advance_char();
                    let end = Span::new(start as u32, self.pos as u32);
                    if !interpolated {
                        return Ok((Token::Str(lit), end));
                    }
                    parts.push(StrPart::Lit(std::mem::take(&mut lit)));
                    return Ok((Token::InterpStr(parts), end));
                }
                Some('{') => {
                    self.advance_char();
                    if self.peek_char() == Some('{') {
                        self.advance_char();
                        lit.push('{');
                        continue;
                    }
                    interpolated = true;
                    parts.push(StrPart::Lit(std::mem::take(&mut lit)));
                    let expr_start = self.pos;
                    self.scan_interp_expr_body(start)?;
                    let expr_end = self.pos;
                    let raw = self.src[expr_start..expr_end].to_owned();
                    self.advance_char(); // the matching '}', left unconsumed by the scan above
                    parts.push(StrPart::Expr(
                        raw,
                        Span::new(expr_start as u32, expr_end as u32),
                    ));
                }
                Some('}') => {
                    self.advance_char();
                    if self.peek_char() == Some('}') {
                        self.advance_char();
                        lit.push('}');
                    } else {
                        return Err(CompileError::InvalidInterpolation {
                            reason: "`}` with no matching `{` — write `}}` for a literal `}`"
                                .to_owned(),
                            span: Span::new(self.pos as u32 - 1, self.pos as u32),
                        });
                    }
                }
                Some('\\') => {
                    let escape_start = self.pos;
                    self.advance_char();
                    lit.push(self.scan_escape(escape_start)?);
                }
                Some(c) => {
                    self.advance_char();
                    lit.push(c);
                }
            }
        }
    }

    /// Scans forward from the first character of an embedded `{expr}`
    /// interpolation body to the matching unescaped `}`, without consuming
    /// it — `self.pos` ends pointing exactly at that `}`. Tracks
    /// `( [ {`/`) ] }` nesting (all sharing one depth counter — this only
    /// needs to find the right boundary, not fully validate bracket
    /// matching; the recursive re-parse of the extracted text does that)
    /// so a nested call/tuple/set-literal/comprehension doesn't terminate
    /// the scan early, and skips over `'...'`/`"..."` literals verbatim
    /// (escapes included) so a brace/paren inside one of those — including
    /// a further nested interpolation — doesn't miscount.
    fn scan_interp_expr_body(&mut self, str_start: usize) -> Result<(), CompileError> {
        let mut depth: i32 = 0;
        loop {
            match self.peek_char() {
                None => {
                    return Err(CompileError::InvalidInterpolation {
                        reason: "unterminated `{` — no matching `}` before the string ended"
                            .to_owned(),
                        span: Span::new(str_start as u32, self.pos as u32),
                    });
                }
                Some('}') if depth == 0 => return Ok(()),
                Some('}') => {
                    depth -= 1;
                    self.advance_char();
                }
                Some('{' | '(' | '[') => {
                    depth += 1;
                    self.advance_char();
                }
                Some(')' | ']') => {
                    depth -= 1;
                    self.advance_char();
                }
                Some('\'') => self.skip_char_literal_verbatim()?,
                Some('"') => self.skip_string_literal_verbatim()?,
                Some(_) => {
                    self.advance_char();
                }
            }
        }
    }

    /// Skips over a `'...'` char literal without decoding it, for the
    /// benefit of `scan_interp_expr_body`'s brace-depth scan — a literal
    /// `'{'`/`'}'`/`'('`/`')'` must not affect bracket counting.
    fn skip_char_literal_verbatim(&mut self) -> Result<(), CompileError> {
        let start = self.pos;
        self.advance_char(); // opening '\''
        match self.peek_char() {
            None | Some('\n') => {
                return Err(CompileError::UnterminatedLiteral {
                    quote: '\'',
                    span: Span::new(start as u32, self.pos as u32),
                });
            }
            Some('\\') => {
                self.advance_char();
                self.advance_char();
            }
            Some(_) => {
                self.advance_char();
            }
        }
        if self.peek_char() == Some('\'') {
            self.advance_char();
            Ok(())
        } else {
            Err(CompileError::UnterminatedLiteral {
                quote: '\'',
                span: Span::new(start as u32, self.pos as u32),
            })
        }
    }

    /// Skips over a `"..."` string literal without decoding it — same
    /// reasoning as `skip_char_literal_verbatim`. Deliberately does not
    /// recurse into its own `{expr}` interpolation chunks (if any): the
    /// brace-depth scan here only needs the *outer* string's closing quote,
    /// nested interpolation is re-discovered independently when this
    /// substring is itself re-lexed later.
    fn skip_string_literal_verbatim(&mut self) -> Result<(), CompileError> {
        let start = self.pos;
        self.advance_char(); // opening '"'
        loop {
            match self.peek_char() {
                None | Some('\n') => {
                    return Err(CompileError::UnterminatedLiteral {
                        quote: '"',
                        span: Span::new(start as u32, self.pos as u32),
                    });
                }
                Some('"') => {
                    self.advance_char();
                    return Ok(());
                }
                Some('\\') => {
                    self.advance_char();
                    self.advance_char();
                }
                Some(_) => {
                    self.advance_char();
                }
            }
        }
    }

    fn scan_ident_or_keyword(&mut self, start: usize) -> (Token, Span) {
        while matches!(self.peek_char(), Some(c) if c.is_alphanumeric() || c == '_') {
            self.advance_char();
        }
        let word = &self.src[start..self.pos];
        let tok = match word {
            "true" => Token::True,
            "false" => Token::False,
            "not" => Token::Not,
            "and" => Token::And,
            "or" => Token::Or,
            "in" => Token::In,
            "rem" => Token::Rem,
            "quot" => Token::Quot,
            "if" => Token::If,
            "then" => Token::Then,
            "else" => Token::Else,
            "mut" => Token::Mut,
            "assert" => Token::Assert,
            "assume" => Token::Assume,
            "require" => Token::Require,
            "alias" => Token::Alias,
            "distinct" => Token::Distinct,
            "equiv" => Token::Equiv,
            "while" => Token::While,
            "for" => Token::For,
            "fail" => Token::Fail,
            "none" => Token::NoneLit,
            "return" => Token::Return,
            "from" => Token::From,
            "size" => Token::Size,
            "_" => Token::Underscore,
            _ => Token::Ident(word.to_owned()),
        };
        (tok, Span::new(start as u32, self.pos as u32))
    }

    /// Consume and return the next token with its source span.
    ///
    /// At paren-depth 0, `\n` emits `Token::Newline` (statement terminator).
    /// At depth > 0, `\n` is silently skipped so multi-line sub-expressions inside
    /// `(...)` work without special syntax.  `{` does not affect depth — set literal
    /// parsers call `skip_newlines()` explicitly between elements.
    pub fn next_token(&mut self) -> Result<(Token, Span), CompileError> {
        loop {
            self.skip_whitespace();
            let start = self.pos;

            if self.peek_char() == Some('\n') {
                self.advance_char();
                if self.paren_depth == 0 {
                    return Ok((Token::Newline, Span::new(start as u32, self.pos as u32)));
                }
                continue;
            }

            let ch = match self.advance_char() {
                None => return Ok((Token::Eof, Span::new(start as u32, start as u32))),
                Some(c) => c,
            };

            let tok = match ch {
                '0'..='9' => return self.scan_int(start),
                c if c.is_alphabetic() || c == '_' => {
                    return Ok(self.scan_ident_or_keyword(start));
                }
                '\'' => return self.scan_char_literal(start),
                '"' => return self.scan_string_literal(start),
                '+' => {
                    if self.peek_char() == Some('+') {
                        self.advance_char();
                        Token::PlusPlus
                    } else {
                        Token::Plus
                    }
                }
                '*' => Token::Star,
                '/' => Token::Slash,
                '|' => Token::Pipe,
                '^' => Token::Caret,
                '&' => Token::Amp,
                '(' => {
                    self.paren_depth += 1;
                    Token::LParen
                }
                ')' => {
                    self.paren_depth = self.paren_depth.saturating_sub(1);
                    Token::RParen
                }
                '[' => {
                    self.paren_depth += 1;
                    Token::LBracket
                }
                ']' => {
                    self.paren_depth = self.paren_depth.saturating_sub(1);
                    Token::RBracket
                }
                '{' => Token::LBrace,
                '}' => Token::RBrace,
                ',' => Token::Comma,
                '?' => Token::Question,
                '.' => Token::Dot,
                ':' => {
                    if self.peek_char() == Some('=') {
                        self.advance_char();
                        Token::ColonEq
                    } else {
                        Token::Colon
                    }
                }
                '-' => {
                    if self.peek_char() == Some('>') {
                        self.advance_char();
                        Token::Arrow
                    } else if self.peek_char() == Some('-') {
                        while !matches!(self.peek_char(), Some('\n') | None) {
                            self.advance_char();
                        }
                        continue; // \n still in stream; loop handles it
                    } else {
                        Token::Minus
                    }
                }
                '=' => {
                    if self.peek_char() == Some('=') {
                        self.advance_char();
                        Token::EqEq
                    } else {
                        Token::Eq
                    }
                }
                '!' => {
                    if self.peek_char() == Some('=') {
                        self.advance_char();
                        Token::BangEq
                    } else if self.peek_char() == Some('!') {
                        self.advance_char();
                        Token::BangBang
                    } else {
                        return Err(CompileError::UnexpectedToken {
                            expected: "`!=` or `!!`".into(),
                            found: "!".into(),
                            span: Span::new(start as u32, self.pos as u32),
                        });
                    }
                }
                '<' => {
                    if self.peek_char() == Some('=') {
                        self.advance_char();
                        Token::LtEq
                    } else {
                        Token::Lt
                    }
                }
                '>' => {
                    if self.peek_char() == Some('=') {
                        self.advance_char();
                        Token::GtEq
                    } else {
                        Token::Gt
                    }
                }
                other => {
                    return Err(CompileError::UnexpectedToken {
                        expected: "a valid token".into(),
                        found: format!("`{other}`"),
                        span: Span::new(start as u32, self.pos as u32),
                    });
                }
            };

            return Ok((tok, Span::new(start as u32, self.pos as u32)));
        }
    }
}
