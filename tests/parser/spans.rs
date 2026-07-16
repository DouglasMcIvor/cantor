use cantor::parser::parse_expr;
use cantor::span::offset_to_line_col;

// ── Spans ─────────────────────────────────────────────────────────────────────

#[test]
fn span_of_integer_literal() {
    let expr = parse_expr("  42  ").unwrap();
    assert_eq!(expr.span.start, 2);
    assert_eq!(expr.span.end, 4);
}

#[test]
fn span_covers_binop() {
    // "1 + 2" → span should cover the whole expression
    let expr = parse_expr("1 + 2").unwrap();
    assert_eq!(expr.span.start, 0);
    assert_eq!(expr.span.end, 5);
}

// ── offset_to_line_col ────────────────────────────────────────────────────────

#[test]
fn line_col_start_of_file() {
    assert_eq!(offset_to_line_col("hello", 0), (1, 1));
}

#[test]
fn line_col_mid_first_line() {
    //                               0123
    assert_eq!(offset_to_line_col("abcd", 2), (1, 3));
}

#[test]
fn line_col_start_of_second_line() {
    // "ab\ncd" — offset 3 is the 'c'
    assert_eq!(offset_to_line_col("ab\ncd", 3), (2, 1));
}

#[test]
fn line_col_mid_second_line() {
    // "ab\ncd" — offset 4 is the 'd'
    assert_eq!(offset_to_line_col("ab\ncd", 4), (2, 2));
}

#[test]
fn line_col_third_line() {
    // "a\nb\nc" — offset 4 is the 'c'
    assert_eq!(offset_to_line_col("a\nb\nc", 4), (3, 1));
}

#[test]
fn line_col_at_newline_char() {
    // The newline itself is on line 1, at the column after 'ab'
    assert_eq!(offset_to_line_col("ab\ncd", 2), (1, 3));
}

#[test]
fn line_col_clamped_to_end() {
    // Offset past end should clamp gracefully.
    let src = "hi";
    let (line, col) = offset_to_line_col(src, 999);
    assert_eq!(line, 1);
    assert_eq!(col, 3); // one past the last char
}

#[test]
fn line_col_parse_error_location() {
    use cantor::parser::parse_file;
    // "f : Int -> Int\nf(x) = @@@"
    // '@' is at line 2, column 8
    let src = "f : Int -> Int\nf(x) = @@@";
    let err = parse_file(src).unwrap_err();
    assert_eq!(err.location(src), Some((2, 8)));
}
