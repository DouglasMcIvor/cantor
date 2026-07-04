//! Elaborator tests: the position-disambiguation cases that caused real bugs
//! before elaboration existed (the lhs/rhs swap, `+` always assuming
//! set-builder context) — `A * B` in domain position must mean Cartesian
//! product while `a * b` in a body means multiplication, `{0} + NatPos` must
//! stay tagged (forced-disjoint), and aliases must resolve transparently.

use cantor::ast::{Item, Param};
use cantor::kind::Kind;
use cantor::parser::parse_file;
use cantor::semantics::elaborate::{check_overload_kind_agreement, elaborate};
use cantor::semantics::tree::{
    SemExpr, SemExprKind, SemFunctionBody, SemFunctionDef, SemFunctionSig, SemItem, SemStmt,
};
use cantor::span::{Span, Symbol};

fn elaborate_src(src: &str) -> Vec<SemItem> {
    let items: Vec<Item> = parse_file(src).unwrap_or_else(|e| panic!("parse error: {e}"));
    elaborate(&items).unwrap_or_else(|e| panic!("elaborate error: {e}"))
}

/// Elaborates `src` and returns the function named `name` — tolerates extra
/// `NameDef` items (aliases, distinct sets) alongside the function under test.
fn elaborate_function(src: &str, name: &str) -> cantor::semantics::tree::SemFunctionDef {
    let items = elaborate_src(src);
    items
        .into_iter()
        .find_map(|item| match item {
            SemItem::FunctionDef(def) if def.name.0 == name => Some(def),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no function named `{name}` in elaborated output"))
}

fn only_function(src: &str) -> cantor::semantics::tree::SemFunctionDef {
    let items = elaborate_src(src);
    assert_eq!(items.len(), 1, "expected exactly one item");
    let SemItem::FunctionDef(def) = items.into_iter().next().unwrap() else {
        panic!("expected a FunctionDef item");
    };
    def
}

// ── `*` disambiguation: Cartesian product (domain) vs multiplication (body) ──

#[test]
fn star_in_domain_is_cartesian_product() {
    let def = only_function("f : Int * Bool -> Int\nf(a, b) = 0");
    let domain = def.sigs[0].domain.as_ref().expect("domain");
    assert!(
        matches!(domain.kind, SemExprKind::CartesianProduct(_, _)),
        "expected CartesianProduct, got {:?}",
        domain.kind
    );
    // Asymmetric arms confirm lhs/rhs aren't swapped (the bug fixed last session).
    assert_eq!(domain.kind_of, Kind::Tuple(vec![Kind::Int, Kind::Bool]));
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int, Kind::Bool]);
}

#[test]
fn star_in_body_is_multiplication() {
    let def = only_function("f : Int * Int -> Int\nf(a, b) = a * b");
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert!(
        matches!(body.kind, SemExprKind::Mul(_, _)),
        "expected Mul, got {:?}",
        body.kind
    );
    assert_eq!(body.kind_of, Kind::Int);
}

#[test]
fn same_function_disambiguates_plus_per_position() {
    // The domain's `+` is a disjoint union (forced-tagged); the body's `+`
    // on the very same parameter is ordinary arithmetic. One function,
    // both meanings, resolved purely from where each `+` appears.
    let def = only_function("h : {0} + NatPos -> Int\nh(x) = x + 1");

    let domain = def.sigs[0].domain.as_ref().expect("domain");
    assert!(
        matches!(domain.kind, SemExprKind::DisjointUnion(_, _)),
        "expected DisjointUnion, got {:?}",
        domain.kind
    );
    assert_eq!(
        domain.kind_of,
        Kind::TaggedUnion(vec![Kind::Int, Kind::Int])
    );
    assert_eq!(
        def.sigs[0].param_kinds,
        vec![Kind::TaggedUnion(vec![Kind::Int, Kind::Int])]
    );

    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert!(
        matches!(body.kind, SemExprKind::Add(_, _)),
        "expected Add, got {:?}",
        body.kind
    );
    assert_eq!(body.kind_of, Kind::Int);
}

// ── `+` forces a tag even when both arms share a Kind (mirrors `distinct`) ───

#[test]
fn disjoint_union_stays_tagged_for_same_kind_arms() {
    let def = only_function("accept_nat : {0} + NatPos -> Nat\naccept_nat(x) = x");
    assert_eq!(
        def.sigs[0].param_kinds,
        vec![Kind::TaggedUnion(vec![Kind::Int, Kind::Int])]
    );
}

// ── `|` collapses same-kind arms (no tag), unlike `+` ────────────────────────

#[test]
fn union_of_same_kind_collapses_no_tag() {
    let def = only_function("g : Nat | NatPos -> Int\ng(x) = x");
    let domain = def.sigs[0].domain.as_ref().expect("domain");
    assert!(matches!(
        &domain.kind,
        SemExprKind::BinOp {
            op: cantor::ast::BinOp::Union,
            ..
        }
    ));
    assert_eq!(domain.kind_of, Kind::Int);
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int]);
}

// ── Aliases resolve transparently through the symbol table ──────────────────

#[test]
fn alias_resolves_to_underlying_kind() {
    let def = elaborate_function("MyNat = Nat\nf : MyNat -> MyNat\nf(x) = x", "f");
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int]);
    assert_eq!(def.sigs[0].return_kind, Kind::Int);
}

#[test]
fn distinct_set_is_int_backed_but_disjoint() {
    let def = elaborate_function("Litre = distinct Nat\nf : Litre -> Litre\nf(x) = x", "f");
    assert_eq!(def.sigs[0].param_kinds, vec![Kind::Int]);
}

// ── Block bodies: `let` constraints are set position, values are value position ─

#[test]
fn let_constraint_is_set_position_value_is_value_position() {
    let def =
        only_function("f : Int * Int -> Int\nf(a, b) {\n s : Int * Int = (a, b)\n s.0 * s.1\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::Let {
        constraint, value, ..
    } = &stmts[0]
    else {
        panic!("expected a Let statement, got {:?}", stmts[0])
    };
    // `Int * Int` constraint → Cartesian product (set position).
    assert!(matches!(
        constraint.kind,
        SemExprKind::CartesianProduct(_, _)
    ));
    assert_eq!(constraint.kind_of, Kind::Tuple(vec![Kind::Int, Kind::Int]));
    // `(a, b)` value → an ordinary tuple value (value position).
    assert!(matches!(value.kind, SemExprKind::Tuple(_)));
}

// ── `in`'s RHS is always set position, even inside a value-position body ────

#[test]
fn in_rhs_is_set_position_regardless_of_surrounding_position() {
    let def = only_function("f : Int -> Bool\nf(x) = x * 2 in NatPos");
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    let SemExprKind::BinOp {
        op: cantor::ast::BinOp::In,
        lhs,
        rhs,
    } = &body.kind
    else {
        panic!("expected a top-level `in`, got {:?}", body.kind)
    };
    // LHS (`x * 2`) is a value-position multiplication.
    assert!(matches!(lhs.kind, SemExprKind::Mul(_, _)));
    // RHS (`NatPos`) is resolved as a set, not a local variable lookup.
    assert_eq!(rhs.kind_of, Kind::Int);
    assert_eq!(body.kind_of, Kind::Bool);
}

// ── Stage 2a: `if`/`++`/vector-indexing gaps closed via kind::merge_* ───────

#[test]
fn if_merges_tuple_and_scalar_branches_into_tagged_union() {
    // Neither branch is already a TaggedUnion, but one is a Tuple — merges
    // into a fresh 2-arm union (mirrors codegen's `IfMerge::NewTaggedUnion`).
    let def = only_function("f : Nat -> (Nat * Nat) | Nat\nf(x) = if x > 0 then (x, x) else x");
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert_eq!(
        body.kind_of,
        Kind::TaggedUnion(vec![Kind::Tuple(vec![Kind::Int, Kind::Int]), Kind::Int])
    );
}

#[test]
fn if_extends_existing_tagged_union_with_new_arm() {
    // `then` is already a 2-arm TaggedUnion (from the inner `if`); `else` is a
    // plain Bool appended as a third arm (mirrors `IfMerge::AppendElseArm`).
    let def = only_function(
        "f : Nat -> (Nat * Nat) | Nat | Bool\nf(x) = if x > 2 then (if x > 5 then (x, x) else x) else false",
    );
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert_eq!(
        body.kind_of,
        Kind::TaggedUnion(vec![
            Kind::Tuple(vec![Kind::Int, Kind::Int]),
            Kind::Int,
            Kind::Bool
        ])
    );
}

#[test]
fn if_merges_two_different_tagged_unions() {
    // Both branches are already (different) TaggedUnions — arms dedup, then's
    // arms first (mirrors `IfMerge::MergeTaggedUnions`).
    let def = only_function(
        "f : Nat -> (Nat * Nat) | Nat | Bool\n\
         f(x) = if x > 3 then (if x > 5 then (x, x) else x) else (if x > 1 then false else (x, x + 1))",
    );
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert_eq!(
        body.kind_of,
        Kind::TaggedUnion(vec![
            Kind::Tuple(vec![Kind::Int, Kind::Int]),
            Kind::Int,
            Kind::Bool
        ])
    );
}

#[test]
fn if_with_unmergeable_branch_kinds_fails_loudly() {
    // Int vs Bool, neither a Tuple nor a TaggedUnion — no coercion path
    // exists, so elaboration must error rather than guess a Kind.
    let items = parse_file("f : Nat -> Int\nf(x) = if x > 0 then 1 else true")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(
        elaborate(&items).is_err(),
        "expected elaborate to reject unmergeable if-branches"
    );
}

#[test]
fn concat_coerces_tuple_literal_to_vector() {
    // lhs is a literal Tuple; rhs (`xs`, constrained to `Nat*`) is already a
    // Vector — lhs must be coerced, and the result Kind is the shared Vector
    // element Kind.
    let def = only_function("f : Nat -> Nat*\nf(x) {\n xs : Nat* = [x]\n (x, x) ++ xs\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(e.kind_of, Kind::Vector(Box::new(Kind::Int)));
}

#[test]
fn indexing_vector_of_tuples_yields_the_tuple_kind_unchanged() {
    let def = only_function("f : -> Nat\nf() {\n xs : (Nat * Nat)* = [(1, 2), (3, 4)]\n xs[0]\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(e.kind_of, Kind::Tuple(vec![Kind::Int, Kind::Int]));
}

#[test]
fn indexing_vector_of_tagged_unions_yields_the_union_kind_unchanged() {
    let def =
        only_function("f : -> Nat\nf() {\n xs : (Nat | (Nat * Bool))* = [1, (2, true)]\n xs[0]\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(
        e.kind_of,
        Kind::TaggedUnion(vec![Kind::Int, Kind::Tuple(vec![Kind::Int, Kind::Bool])])
    );
}

// ── Prerequisites found while planning Stage 2b ─────────────────────────────

#[test]
fn fallible_range_return_kind_is_the_fail_struct_not_the_bare_union() {
    // `Nat -> Nat !! HTTPError` desugars to a range whose Kind must be the
    // {Fail, payload} wrapper (mirrors codegen's `wire::range_kind`, now
    // shared via `kind::range_kind`) — plain `set_kind` would ignore the
    // Fail arm and give just the payload's Kind.
    let items = parse_file("HTTPError = {400, 503}\nfetch : Nat -> Nat !! HTTPError\nfetch(x) = x")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    let items = elaborate(&items).unwrap_or_else(|e| panic!("elaborate error: {e}"));
    let def = items
        .into_iter()
        .find_map(|item| match item {
            SemItem::FunctionDef(def) if def.name.0 == "fetch" => Some(def),
            _ => None,
        })
        .expect("no function named `fetch`");
    assert_eq!(def.return_kind, Kind::Tuple(vec![Kind::Fail, Kind::Int]));
    assert_eq!(
        def.sigs[0].return_kind,
        Kind::Tuple(vec![Kind::Fail, Kind::Int])
    );
}

#[test]
fn for_in_over_runtime_set_variable_does_not_treat_it_as_a_set_description() {
    // `s` here is a local variable of Kind::Set(Int), not a named set — the
    // ForIn iterable must be elaborated as a value (a variable lookup), not
    // as a set-position expression (which would try `set_kind` on a local
    // name and panic with "unknown set name").
    let def = only_function(
        "f : -> Int\nf() {\n mut s : Set(Int) = {1, 2, 3}\n mut acc : Int = 0\n for x in s {\n acc := acc + x\n }\n acc\n}",
    );
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::ForIn { set, .. } = &stmts[2] else {
        panic!("expected a ForIn statement, got {:?}", stmts[2])
    };
    assert!(
        matches!(set.kind, SemExprKind::Var(_)),
        "expected a Var node, got {:?}",
        set.kind
    );
    assert_eq!(set.kind_of, Kind::Set(cantor::kind::SetElemKind::Int));
}

#[test]
fn for_in_over_set_literal_elaborates_elements_as_arithmetic_not_disjoint_union() {
    // The literal's elements must stay ordinary value-position arithmetic
    // (`n + 1` as Add) rather than becoming a set-position DisjointUnion —
    // `compile_for_in` compiles each element with `compile_expr` (value
    // semantics) regardless of how the literal itself is classified.
    let def = only_function("f : Int -> Int\nf(n) {\n for x in {n, n + 1} {\n }\n 0\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::ForIn { set, .. } = &stmts[0] else {
        panic!("expected a ForIn statement, got {:?}", stmts[0])
    };
    let SemExprKind::SetLit(elements) = &set.kind else {
        panic!("expected a SetLit, got {:?}", set.kind)
    };
    assert!(
        matches!(elements[1].kind, SemExprKind::Add(_, _)),
        "expected Add, got {:?}",
        elements[1].kind
    );
}

#[test]
fn for_in_over_empty_set_literal_does_not_error() {
    // Zero elements means the element Kind can't be inferred, but the body
    // never actually runs (codegen unrolls a SetLit iterable at compile
    // time) — this must not error the way an empty value-position SetLit
    // elsewhere legitimately does.
    let def = only_function("f : -> Int\nf() {\n for x in {} {\n }\n 0\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let cantor::semantics::tree::SemStmt::ForIn { set, .. } = &stmts[0] else {
        panic!("expected a ForIn statement, got {:?}", stmts[0])
    };
    assert!(matches!(&set.kind, SemExprKind::SetLit(elements) if elements.is_empty()));
}

// ── Prerequisites found while wiring `elaborate()` into the real codegen
// pipeline (Stage 2b) — all four were previously unreachable because nothing
// but elaborate_tests.rs itself called `elaborate()` on real programs.

#[test]
fn membership_rhs_local_runtime_set_variable_is_value_position() {
    // `primes` here is a local `mut ... : Set(Int)` variable, not a named
    // set — `in`'s RHS must be Position::Value (an env lookup) for it,
    // mirroring codegen::compile_binop's own env-first dispatch. Treating
    // it as Position::Set unconditionally panics via `set_kind`'s "unknown
    // set name" (there's no NameDef for a local).
    let def =
        only_function("f : -> Bool\nf() {\n mut primes : Set(Int) = {2, 3, 5}\n 3 in primes\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    let SemExprKind::BinOp {
        op: cantor::ast::BinOp::In,
        rhs,
        ..
    } = &e.kind
    else {
        panic!("expected a top-level `in`, got {:?}", e.kind)
    };
    assert!(matches!(rhs.kind, SemExprKind::Var(_)));
    assert_eq!(rhs.kind_of, Kind::Set(cantor::kind::SetElemKind::Int));
}

#[test]
fn builtin_len_call_is_not_treated_as_an_undeclared_function() {
    // `len`/`size`/`from`/auto-generated `distinct` constructors are
    // recognized by name directly in codegen::compile_call and never
    // appear in `fn_sigs` — calling them must not error as "undeclared".
    let def = only_function("f : Nat* -> Nat\nf(xs) = len(xs)");
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert_eq!(body.kind_of, Kind::Int);
}

#[test]
fn unconstrained_destructuring_binding_gets_a_kind_from_the_tuple_value() {
    // `x, y = (p.0, p.1)` has no per-binding `: Type` annotations — the
    // binding Kind must come from the value's Tuple element Kinds (mirrors
    // codegen::blocks's DestructLet handling, which never even looks at
    // constraints for Kind purposes), not be left unbound.
    let def = only_function("f : Int * Int -> Int\nf(p) {\n x, y = (p.0, p.1)\n x + y\n}");
    let SemFunctionBody::Block(stmts) = &def.body else {
        panic!("expected block body")
    };
    let SemStmt::Expr(e) = &stmts[1] else {
        panic!("expected an Expr statement, got {:?}", stmts[1])
    };
    assert_eq!(e.kind_of, Kind::Int);
}

#[test]
fn value_position_var_falls_back_to_a_top_level_scalar_constant() {
    // `base` is a top-level annotated constant (`base : Nat = 10`), not a
    // local — referencing it from another function's body must resolve via
    // `name_defs`, not just the local `env`.
    let def = elaborate_function(
        "base : Nat = 10\nadd_base : Nat -> Nat\nadd_base(x) = x + base",
        "add_base",
    );
    let SemFunctionBody::Expr(body) = &def.body else {
        panic!("expected expr body")
    };
    assert_eq!(body.kind_of, Kind::Int);
}

// ── int-soundness-plan phase 2: overload sets (multiple bodies, one name) ────

/// Confirms `elaborate()`'s current behaviour ahead of phase 2: two top-level
/// `FunctionDef`s sharing a name already parse as two distinct items (see
/// tests/funcdef_tests.rs::two_function_defs_same_name_parse_as_separate_items),
/// and `elaborate()` maps over every item unconditionally — both bodies do
/// already survive into the returned `Vec<SemItem>` today, with no grouping
/// or validation applied to them at all. (The last-wins collapsing that
/// actually drops a body lives further downstream, in
/// `solver::FunctionEnv`/`codegen`'s name-keyed maps, not here.)
#[test]
fn two_same_name_function_defs_both_survive_elaboration_untouched() {
    let items = elaborate_src("f : Nat -> Nat\nf(x) = x + 1\nf : Nat -> Nat\nf(x) = x + 2");
    let count = items
        .iter()
        .filter(|item| matches!(item, SemItem::FunctionDef(def) if def.name.0 == "f"))
        .count();
    assert_eq!(
        count, 2,
        "expected both overloads of `f` to survive elaboration"
    );
}

/// Two same-name, same-arity `FunctionDef`s that disagree on the Kind of a
/// position (here: `Int` vs `Bool` return) form an overload set whose
/// members don't agree — `check_overload_kind_agreement` rejects this with
/// `CompileError::OverloadKindMismatch`.
#[test]
fn overloads_with_mismatched_return_kind_are_rejected() {
    let items = parse_file("f : Int -> Int\nf(x) = x\nf : Int -> Bool\nf(x) = true")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(
        elaborate(&items).is_err(),
        "expected elaborate to reject overloads that disagree on return Kind"
    );
}

/// Same check, but the disagreement is in a parameter position instead of
/// the return Kind.
#[test]
fn overloads_with_mismatched_param_kind_are_rejected() {
    let items = parse_file("f : Int -> Int\nf(x) = x\nf : Bool -> Int\nf(x) = 0")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(
        elaborate(&items).is_err(),
        "expected elaborate to reject overloads that disagree on a parameter Kind"
    );
}

/// Overloads of differing arity need no Kind agreement against each other —
/// arity alone is a free, always-static dispatch key (confirmed design
/// choice for phase 2), so `f : Int -> Int` and `f : Int * Int -> Bool` are
/// two independent single-member groups, not one mismatched group.
#[test]
fn overloads_with_different_arity_need_no_kind_agreement() {
    let items = parse_file("f : Int -> Int\nf(x) = x\nf : Int * Int -> Bool\nf(x, y) = x == y")
        .unwrap_or_else(|e| panic!("parse error: {e}"));
    assert!(
        elaborate(&items).is_ok(),
        "differing-arity overloads must not be treated as one Kind-agreement group"
    );
}

// ── `compiler_generated_split` exception (int-soundness-plan phase 3, step 2) ─
//
// Nothing produces `compiler_generated_split = true` anywhere in the real
// pipeline yet — no source syntax sets it, and step 4 (the actual
// `Int64`/`BigInt` split generator) doesn't exist yet either. These tests
// exercise `check_overload_kind_agreement` directly against hand-built
// `SemFunctionDef` fixtures, the same way step 4's generator will one day
// feed it, to prove the exception is exactly as narrow as intended ahead of
// having a real producer to test against.

fn dummy_expr(kind_of: Kind) -> SemExpr {
    SemExpr {
        kind: SemExprKind::IntLit(0),
        kind_of,
        span: Span::dummy(),
    }
}

fn dummy_sig(param_kinds: Vec<Kind>, return_kind: Kind) -> SemFunctionSig {
    SemFunctionSig {
        domain: None,
        range: dummy_expr(return_kind.clone()),
        param_kinds,
        return_kind,
        span: Span::dummy(),
    }
}

fn dummy_def(
    name: &str,
    param_kinds: Vec<Kind>,
    return_kind: Kind,
    compiler_generated_split: bool,
) -> SemItem {
    let params = (0..param_kinds.len())
        .map(|i| Param::new(&format!("p{i}")))
        .collect();
    SemItem::FunctionDef(SemFunctionDef {
        name: Symbol::new(name),
        sigs: vec![dummy_sig(param_kinds.clone(), return_kind.clone())],
        params,
        body: SemFunctionBody::Expr(dummy_expr(return_kind.clone())),
        param_kinds,
        return_kind,
        span: Span::dummy(),
        compiler_generated_split,
    })
}

#[test]
fn compiler_generated_int64_bigint_split_bypasses_kind_agreement() {
    let items = vec![
        dummy_def("foo", vec![Kind::Int], Kind::Int, true),
        dummy_def("foo", vec![Kind::Int64], Kind::Int64, true),
    ];
    assert!(
        check_overload_kind_agreement(&items).is_ok(),
        "a compiler-generated Int64/BigInt pair must be allowed to disagree on Kind"
    );
}

#[test]
fn compiler_generated_split_exception_is_specific_to_int_and_int64() {
    // Both marked, but the mismatch isn't the Int/Int64 pairing — still an error.
    let items = vec![
        dummy_def("foo", vec![Kind::Int], Kind::Int, true),
        dummy_def("foo", vec![Kind::Bool], Kind::Bool, true),
    ];
    assert!(
        check_overload_kind_agreement(&items).is_err(),
        "the compiler_generated_split marker must not excuse arbitrary Kind mismatches"
    );
}

#[test]
fn only_one_overload_marked_compiler_generated_split_still_errors() {
    // The exception requires *both* members marked — a stray/incomplete
    // marker on just one side must not silently widen it.
    let items = vec![
        dummy_def("foo", vec![Kind::Int], Kind::Int, true),
        dummy_def("foo", vec![Kind::Int64], Kind::Int64, false),
    ];
    assert!(
        check_overload_kind_agreement(&items).is_err(),
        "a Kind mismatch must still error when only one overload is marked as the split"
    );
}

#[test]
fn compiler_generated_split_allows_int64_mix_alongside_exact_agreement() {
    // A multi-param signature where one position is the Int/Int64 exception
    // and another position matches exactly (Bool) — both must be handled
    // per-position, not as an all-or-nothing check on the whole group.
    let items = vec![
        dummy_def("foo", vec![Kind::Int, Kind::Bool], Kind::Int, true),
        dummy_def("foo", vec![Kind::Int64, Kind::Bool], Kind::Int64, true),
    ];
    assert!(
        check_overload_kind_agreement(&items).is_ok(),
        "the Int/Int64 exception must apply per-position alongside ordinary exact agreement"
    );
}

#[test]
fn no_source_syntax_sets_compiler_generated_split() {
    // Regression guard: ordinary elaboration of real source must never set
    // the marker, since nothing should be able to reach the exception
    // without going through the (not yet implemented) step 4 generator.
    let items = elaborate_src("f : Int -> Int\nf(x) = x");
    let SemItem::FunctionDef(def) = items.into_iter().next().unwrap() else {
        panic!("expected a FunctionDef item");
    };
    assert!(!def.compiler_generated_split);
}
