use super::helpers::*;

// ── Error cases ───────────────────────────────────────────────────────────────

#[test]
fn parse_empty_is_error() {
    assert!(!parse_err("").is_empty());
}

#[test]
fn parse_dangling_operator_is_error() {
    assert!(!parse_err("1 +").is_empty());
}

#[test]
fn parse_unmatched_paren_is_error() {
    assert!(!parse_err("(1 + 2").is_empty());
}

#[test]
fn parse_for_in_expr_is_error() {
    // bare `for` outside `{...}` is not a valid expression
    let msg = parse_err("for");
    assert!(msg.contains("for"), "expected 'for' in error: {msg}");
}
