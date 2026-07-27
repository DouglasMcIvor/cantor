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

// ── Reserved words in identifier position ────────────────────────────────────
// Naming a function after a keyword is an easy mistake to make when the
// keyword reads like an ordinary word (`size`, `from`), and the resulting
// error points at the *following* line's first token, so it's worth saying
// plainly that the word is reserved rather than leaving "found size".

#[test]
fn function_named_after_a_keyword_says_reserved_word() {
    let err = cantor::parser::parse_file("size : Nat -> Nat\nsize(x) = x")
        .expect_err("`size` is a reserved word, so this must not parse");
    let msg = err.to_string();
    assert!(
        msg.contains("reserved word") && msg.contains("size"),
        "expected a reserved-word diagnostic naming `size`, got: {msg}"
    );
}

#[test]
fn set_named_after_a_keyword_says_reserved_word() {
    let err = cantor::parser::parse_file("from = Nat")
        .expect_err("`from` is a reserved word, so this must not parse");
    assert!(
        err.to_string().contains("reserved word"),
        "expected a reserved-word diagnostic, got: {err}"
    );
}

#[test]
fn a_non_keyword_unexpected_token_is_not_called_a_reserved_word() {
    // The reserved-word wording must be specific to keywords, not blanket
    // text on every `expected identifier` failure.
    let err = cantor::parser::parse_file("3 = Nat").expect_err("a literal is not a definition");
    assert!(
        !err.to_string().contains("reserved word"),
        "an integer literal is not a reserved word: {err}"
    );
}

#[test]
fn readme_documents_every_reserved_word() {
    // The list in README's "Reserved words" section is the only place a user
    // can find out that `size` isn't available as a name. A hand-maintained
    // list drifts the moment a keyword is added, so tie it to the lexer's
    // own table rather than trusting whoever adds the next keyword to
    // remember.
    //
    // Deliberately reads only the fenced code block, not the whole section:
    // the surrounding prose names a few keywords as examples, and matching
    // against that made an earlier version of this test pass even with a
    // word deleted from the list it is supposed to be checking.
    let readme = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))
        .expect("README.md must be readable from the crate root");
    let (_, after_heading) = readme
        .split_once("## Reserved words")
        .expect("README must have a `## Reserved words` section");
    let (_, after_fence) = after_heading
        .split_once("```\n")
        .expect("the reserved-words section must contain a fenced list");
    let (listed, _) = after_fence
        .split_once("```")
        .expect("the fenced list must be closed");
    let listed: Vec<&str> = listed.split_whitespace().collect();

    let missing: Vec<_> = cantor::parser::lexer::Token::RESERVED_WORDS
        .iter()
        .filter(|word| !listed.contains(word))
        .collect();
    assert!(
        missing.is_empty(),
        "README's reserved-words list is missing: {missing:?}"
    );

    let extra: Vec<_> = listed
        .iter()
        .filter(|word| !cantor::parser::lexer::Token::RESERVED_WORDS.contains(word))
        .collect();
    assert!(
        extra.is_empty(),
        "README's reserved-words list names words the lexer doesn't reserve: {extra:?}"
    );
}
