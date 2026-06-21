use std::fmt;

use crate::{error::CompileError, span::Span};

/// A single lexical token.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    Int(i64),

    // Keywords — expressions
    True,
    False,
    Not,
    And,
    Or,
    In,
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
    // Loops
    While,
    // Reserved for comprehensions (parser rejects with a "not yet" error)
    For,
    // Failure
    Fail,
    // Built-in functions (reserved — cannot be shadowed by user definitions)
    From,
    Size,

    // Identifiers
    Ident(String),

    // Arithmetic / set-difference
    Plus,   // +
    Minus,  // -  (also set difference; disambiguation is semantic)
    Star,   // *  (also Cartesian product in signature position)
    Slash,  // /

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
    Eq,       // =   (initial binding, pure-body connector)
    ColonEq,  // :=  (reassignment of a `mut` variable)
    Arrow,    // ->  (signature range separator)
    Colon,    // :   (signature type separator)

    // Punctuation
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    Comma,    // ,
    Question, // ?  (postfix propagate-failure operator)

    Eof,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Int(n)   => write!(f, "{n}"),
            Token::Ident(s) => write!(f, "`{s}`"),
            Token::True     => f.write_str("true"),
            Token::False    => f.write_str("false"),
            Token::Not      => f.write_str("not"),
            Token::And      => f.write_str("and"),
            Token::Or       => f.write_str("or"),
            Token::In       => f.write_str("in"),
            Token::If       => f.write_str("if"),
            Token::Then     => f.write_str("then"),
            Token::Else     => f.write_str("else"),
            Token::Mut      => f.write_str("mut"),
            Token::Assert   => f.write_str("assert"),
            Token::Assume   => f.write_str("assume"),
            Token::Require  => f.write_str("require"),
            Token::Return   => f.write_str("return"),
            Token::Alias    => f.write_str("alias"),
            Token::Distinct => f.write_str("distinct"),
            Token::While    => f.write_str("while"),
            Token::For      => f.write_str("for"),
            Token::Fail     => f.write_str("fail"),
            Token::From     => f.write_str("from"),
            Token::Size     => f.write_str("size"),
            Token::Plus     => f.write_str("+"),
            Token::Minus    => f.write_str("-"),
            Token::Star     => f.write_str("*"),
            Token::Slash    => f.write_str("/"),
            Token::Pipe     => f.write_str("|"),
            Token::BangBang => f.write_str("!!"),
            Token::Caret    => f.write_str("^"),
            Token::Amp      => f.write_str("&"),
            Token::EqEq     => f.write_str("=="),
            Token::BangEq   => f.write_str("!="),
            Token::Lt       => f.write_str("<"),
            Token::LtEq     => f.write_str("<="),
            Token::Gt       => f.write_str(">"),
            Token::GtEq     => f.write_str(">="),
            Token::Eq       => f.write_str("="),
            Token::ColonEq  => f.write_str(":="),
            Token::Arrow    => f.write_str("->"),
            Token::Colon    => f.write_str(":"),
            Token::LParen   => f.write_str("("),
            Token::RParen   => f.write_str(")"),
            Token::LBrace   => f.write_str("{"),
            Token::RBrace   => f.write_str("}"),
            Token::Comma    => f.write_str(","),
            Token::Question => f.write_str("?"),
            Token::Eof      => f.write_str("<eof>"),
        }
    }
}

/// Stateful lexer. Call `next_token()` repeatedly until `Token::Eof`.
pub struct Lexer<'src> {
    src: &'src str,
    pos: usize,
}

impl<'src> Lexer<'src> {
    pub fn new(src: &'src str) -> Self {
        Self { src, pos: 0 }
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
        while matches!(self.peek_char(), Some(c) if c.is_whitespace()) {
            self.advance_char();
        }
    }

    fn scan_int(&mut self, start: usize) -> Result<(Token, Span), CompileError> {
        while matches!(self.peek_char(), Some(c) if c.is_ascii_digit()) {
            self.advance_char();
        }
        let text = &self.src[start..self.pos];
        let n = text.parse::<i64>().map_err(|_| CompileError::InvalidIntLiteral {
            text: text.to_owned(),
            span: Span::new(start as u32, self.pos as u32),
        })?;
        Ok((Token::Int(n), Span::new(start as u32, self.pos as u32)))
    }

    fn scan_ident_or_keyword(&mut self, start: usize) -> (Token, Span) {
        while matches!(self.peek_char(), Some(c) if c.is_alphanumeric() || c == '_') {
            self.advance_char();
        }
        let word = &self.src[start..self.pos];
        let tok = match word {
            "true"   => Token::True,
            "false"  => Token::False,
            "not"    => Token::Not,
            "and"    => Token::And,
            "or"     => Token::Or,
            "in"     => Token::In,
            "if"     => Token::If,
            "then"   => Token::Then,
            "else"   => Token::Else,
            "mut"      => Token::Mut,
            "assert"   => Token::Assert,
            "assume"   => Token::Assume,
            "require"  => Token::Require,
            "alias"    => Token::Alias,
            "distinct" => Token::Distinct,
            "while"    => Token::While,
            "for"      => Token::For,
            "fail"     => Token::Fail,
            "return"   => Token::Return,
            "from"     => Token::From,
            "size"     => Token::Size,
            _          => Token::Ident(word.to_owned()),
        };
        (tok, Span::new(start as u32, self.pos as u32))
    }

    /// Consume and return the next token with its source span.
    pub fn next_token(&mut self) -> Result<(Token, Span), CompileError> {
        self.skip_whitespace();
        let start = self.pos;

        let ch = match self.advance_char() {
            None => return Ok((Token::Eof, Span::new(start as u32, start as u32))),
            Some(c) => c,
        };

        let tok = match ch {
            '0'..='9' => return self.scan_int(start),
            c if c.is_alphabetic() || c == '_' => {
                return Ok(self.scan_ident_or_keyword(start));
            }
            '+' => Token::Plus,
            '*' => Token::Star,
            '/' => Token::Slash,
            '|' => Token::Pipe,
            '^' => Token::Caret,
            '&' => Token::Amp,
            '(' => Token::LParen,
            ')' => Token::RParen,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ',' => Token::Comma,
            '?' => Token::Question,
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
                    return self.next_token();
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

        Ok((tok, Span::new(start as u32, self.pos as u32)))
    }
}
