use cantor::parser::lexer::{Lexer, Token};

fn lex_all(src: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(src);
    let mut tokens = Vec::new();
    loop {
        let (tok, _) = lexer.next_token().expect("lex error");
        let done = tok == Token::Eof;
        tokens.push(tok);
        if done {
            break;
        }
    }
    tokens
}

// ── Literals ──────────────────────────────────────────────────────────────────

#[test]
fn lex_integer() {
    assert_eq!(lex_all("42"), vec![Token::Int(42), Token::Eof]);
}

#[test]
fn lex_zero() {
    assert_eq!(lex_all("0"), vec![Token::Int(0), Token::Eof]);
}

#[test]
fn lex_large_integer() {
    assert_eq!(lex_all("1000000"), vec![Token::Int(1_000_000), Token::Eof]);
}

// ── Keywords ──────────────────────────────────────────────────────────────────

#[test]
fn lex_bool_keywords() {
    assert_eq!(
        lex_all("true false"),
        vec![Token::True, Token::False, Token::Eof]
    );
}

#[test]
fn lex_logic_keywords() {
    assert_eq!(
        lex_all("not and or"),
        vec![Token::Not, Token::And, Token::Or, Token::Eof]
    );
}

#[test]
fn lex_in_keyword() {
    assert_eq!(lex_all("in"), vec![Token::In, Token::Eof]);
}

#[test]
fn lex_reserved_for_if() {
    assert_eq!(lex_all("for if"), vec![Token::For, Token::If, Token::Eof]);
}

// ── Identifiers ───────────────────────────────────────────────────────────────

#[test]
fn lex_simple_ident() {
    assert_eq!(lex_all("foo"), vec![Token::Ident("foo".into()), Token::Eof]);
}

#[test]
fn lex_ident_with_underscore() {
    assert_eq!(
        lex_all("my_var"),
        vec![Token::Ident("my_var".into()), Token::Eof]
    );
}

#[test]
fn lex_keyword_prefix_not_keyword() {
    // `true_value` is an identifier, not `true` + `_value`
    assert_eq!(
        lex_all("true_value"),
        vec![Token::Ident("true_value".into()), Token::Eof]
    );
}

// ── Operators ─────────────────────────────────────────────────────────────────

#[test]
fn lex_arithmetic() {
    assert_eq!(
        lex_all("+ - * /"),
        vec![
            Token::Plus,
            Token::Minus,
            Token::Star,
            Token::Slash,
            Token::Eof
        ]
    );
}

#[test]
fn lex_set_operators() {
    assert_eq!(
        lex_all("| ^ &"),
        vec![Token::Pipe, Token::Caret, Token::Amp, Token::Eof]
    );
}

#[test]
fn lex_comparisons() {
    assert_eq!(
        lex_all("== != < <= > >="),
        vec![
            Token::EqEq,
            Token::BangEq,
            Token::Lt,
            Token::LtEq,
            Token::Gt,
            Token::GtEq,
            Token::Eof
        ]
    );
}

// ── Punctuation ───────────────────────────────────────────────────────────────

#[test]
fn lex_parens_and_braces() {
    assert_eq!(
        lex_all("( ) { }"),
        vec![
            Token::LParen,
            Token::RParen,
            Token::LBrace,
            Token::RBrace,
            Token::Eof
        ]
    );
}

#[test]
fn lex_comma() {
    assert_eq!(lex_all(","), vec![Token::Comma, Token::Eof]);
}

// ── Whitespace handling ───────────────────────────────────────────────────────

#[test]
fn lex_ignores_whitespace() {
    assert_eq!(
        lex_all("  42   +   1  "),
        vec![Token::Int(42), Token::Plus, Token::Int(1), Token::Eof]
    );
}

#[test]
fn lex_newlines_emit_tokens_at_depth_zero() {
    assert_eq!(
        lex_all("x\n+\ny"),
        vec![
            Token::Ident("x".into()),
            Token::Newline,
            Token::Plus,
            Token::Newline,
            Token::Ident("y".into()),
            Token::Eof,
        ]
    );
}

#[test]
fn lex_newlines_suppressed_inside_parens() {
    assert_eq!(
        lex_all("(\nx\n)"),
        vec![
            Token::LParen,
            Token::Ident("x".into()),
            Token::RParen,
            Token::Eof
        ]
    );
}

#[test]
fn lex_newlines_not_suppressed_inside_braces() {
    assert_eq!(
        lex_all("{\nx\n}"),
        vec![
            Token::LBrace,
            Token::Newline,
            Token::Ident("x".into()),
            Token::Newline,
            Token::RBrace,
            Token::Eof
        ]
    );
}

// ── Spans ─────────────────────────────────────────────────────────────────────

#[test]
fn lex_span_of_integer() {
    let mut lexer = Lexer::new("  42  ");
    let (tok, span) = lexer.next_token().unwrap();
    assert_eq!(tok, Token::Int(42));
    assert_eq!(span.start, 2);
    assert_eq!(span.end, 4);
}

#[test]
fn lex_span_of_two_char_op() {
    let mut lexer = Lexer::new("<=");
    let (tok, span) = lexer.next_token().unwrap();
    assert_eq!(tok, Token::LtEq);
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 2);
}

// ── Bracket delimiters (for homogeneous tuple literals `[...]`) ───────────────
// These tests document the *intended* behaviour once `[` and `]` are added to
// the lexer as Token::LBracket / Token::RBracket.  Until then they assert that
// the characters produce a lex error, so they pass today and will need to be
// updated when the tokens are introduced.

#[test]
fn lex_lbracket() {
    assert_eq!(
        lex_all("[ ]"),
        vec![Token::LBracket, Token::RBracket, Token::Eof]
    );
}

#[test]
fn lex_rbracket() {
    assert_eq!(lex_all("]"), vec![Token::RBracket, Token::Eof]);
}

#[test]
fn lex_array_lit() {
    assert_eq!(
        lex_all("[1, 2, 3]"),
        vec![
            Token::LBracket,
            Token::Int(1),
            Token::Comma,
            Token::Int(2),
            Token::Comma,
            Token::Int(3),
            Token::RBracket,
            Token::Eof,
        ]
    );
}

// ── Error cases ───────────────────────────────────────────────────────────────

#[test]
fn lex_bare_bang_is_error() {
    let mut lexer = Lexer::new("!");
    assert!(lexer.next_token().is_err());
}

#[test]
fn lex_bare_eq_is_token() {
    // `=` is valid: used for `= expr` pure bodies and `mut x = expr` initial bindings.
    let mut lexer = Lexer::new("=");
    let (tok, _) = lexer.next_token().unwrap();
    assert_eq!(tok, cantor::parser::lexer::Token::Eq);
}

#[test]
fn lex_colon_eq_is_reassignment_token() {
    assert_eq!(lex_all(":="), vec![Token::ColonEq, Token::Eof]);
}

#[test]
fn lex_colon_eq_distinguished_from_colon() {
    // `:` alone is Colon; `:=` is ColonEq.
    assert_eq!(
        lex_all(": :="),
        vec![Token::Colon, Token::ColonEq, Token::Eof]
    );
}

#[test]
fn lex_unknown_char_is_error() {
    let mut lexer = Lexer::new("@");
    assert!(lexer.next_token().is_err());
}

// ── Comments ──────────────────────────────────────────────────────────────────

#[test]
fn line_comment_skipped() {
    // The comment itself is discarded; the \n after it emits Newline at depth 0.
    assert_eq!(
        lex_all("-- this is a comment\n42"),
        vec![Token::Newline, Token::Int(42), Token::Eof]
    );
}

#[test]
fn inline_comment_skipped() {
    assert_eq!(
        lex_all("x + 1 -- add one"),
        vec![
            Token::Ident("x".into()),
            Token::Plus,
            Token::Int(1),
            Token::Eof
        ]
    );
}

#[test]
fn comment_at_eof_skipped() {
    assert_eq!(lex_all("-- no newline at end"), vec![Token::Eof]);
}

#[test]
fn comment_does_not_consume_next_line() {
    assert_eq!(
        lex_all("1 -- first\n2"),
        vec![Token::Int(1), Token::Newline, Token::Int(2), Token::Eof]
    );
}
