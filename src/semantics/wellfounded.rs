//! Well-foundedness check for recursive named-set definitions
//! (design-decisions.md §3, "Recursive sets" — tier 1, structural recursion
//! only; docs/recursive-sets-plan.md Phase 0).
//!
//! Runs before any other elaboration step, because the failure mode it
//! guards against isn't a bad diagnostic — it's `kind::set_kind`/
//! `kind::set_sort` recursing forever the moment they resolve a
//! `DefKind::Alias` whose value refers back to itself, directly or through
//! a chain of other aliases. Two layers:
//!
//! 1. **Generic cycle detection** (`find_cyclic_names`) — a plain
//!    reachability walk over every `Var` reference reachable from a name's
//!    definition, regardless of which operator it sits under. This is the
//!    safety net: every possible infinite-recursion shape is caught here,
//!    full stop, before layer 2 even runs.
//! 2. **Tier-1 shape classification** (`classify`) — only for names layer 1
//!    flagged. Splits each definition into `|`-arms and, within each arm,
//!    `*`-factors (`ast::flatten_union`/`ast::flatten_domain`), then runs
//!    the "generating sets" fixpoint sketched in backlog.md: a name becomes
//!    generating once at least one of its arms is built entirely from
//!    already-generating names and/or non-recursive bases. A cyclic name
//!    whose recursive reference doesn't show up as a bare arm/factor
//!    (nested under `&`, `-`, a comprehension, …) is classified
//!    `Unrecognized` rather than silently folded into either outcome.
//!
//! **Correction from the first draft of docs/recursive-sets-plan.md**: the
//! rule is *not* "every recursive occurrence must be a direct operand of
//! `*`". Cantor's cross-kind unions already give every arm — bare or
//! compound — its own CVC5 constructor (`build_union_datatype_sort` in
//! `solver/sort.rs`), so a bare self-reference arm (`Peano = Zero | Peano`,
//! unary Nat) is exactly as well-founded as a product-guarded one
//! (`Tree = Int | Tree * Tree`). The only real requirement, matching
//! backlog.md's original sketch, is that at least one arm per name in the
//! cycle bottoms out without needing itself.

use std::collections::{HashMap, HashSet};

use crate::ast::{DefKind, Expr, ExprKind, Item, NameDefs, flatten_domain, flatten_union};
use crate::error::CompileError;
use crate::span::Symbol;

/// Entry point — called once per file, before any other elaboration step.
pub fn check_well_founded(items: &[Item], name_defs: &NameDefs) -> Result<(), CompileError> {
    let raw_deps = build_raw_dep_graph(name_defs);
    let cyclic_names = find_cyclic_names(&raw_deps);
    if cyclic_names.is_empty() {
        return Ok(());
    }

    let (generating, unrecognized) = classify(&cyclic_names, name_defs);

    // Walk `items` (source order), not the HashMap, so which offending name
    // gets reported first is deterministic across runs.
    for item in items {
        let Item::NameDef(def) = item else { continue };
        if !cyclic_names.contains(&def.name) {
            continue;
        }
        if unrecognized.contains(&def.name) {
            return Err(CompileError::Unsupported {
                feature: format!(
                    "recursive set `{}` — the recursive reference isn't a bare union \
                     arm or Cartesian-product factor; non-structural recursion (tier \
                     2/3, `decreasing by`) isn't supported yet, see design-decisions.md §3",
                    def.name.0
                ),
                span: def.span,
            });
        }
        if !generating.contains(&def.name) {
            return Err(CompileError::IllFoundedRecursiveSet {
                name: def.name.0.clone(),
                span: def.span,
            });
        }
        // Well-founded and shape-recognized (tier 1), but the Kind/solver
        // representation for actually compiling one doesn't exist yet.
        // TODO(docs/recursive-sets-plan.md phases 1-3): CVC5 self-referential
        // datatype encoding, boxed runtime representation, narrowing/
        // consumption. Fail loudly rather than falling through to whatever
        // `set_kind` would otherwise (incorrectly) do with this name.
        return Err(CompileError::Unsupported {
            feature: format!(
                "recursive set `{}` is well-founded, but recursive-set codegen/solver \
                 support isn't implemented yet (see docs/recursive-sets-plan.md)",
                def.name.0
            ),
            span: def.span,
        });
    }
    Ok(())
}

/// Visit every `Var` symbol anywhere inside `expr`. The one generic
/// recursive-descent primitive both the cycle-detection graph and the
/// arm/factor shape classifier are built on — a future `ExprKind` variant
/// only needs handling once, here, exhaustively (no wildcard arm).
fn for_each_var(expr: &Expr, f: &mut impl FnMut(&Symbol)) {
    match &expr.kind {
        ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::CharLit(_) | ExprKind::FailLit => {}
        ExprKind::Var(sym) => f(sym),
        ExprKind::BinOp { lhs, rhs, .. } => {
            for_each_var(lhs, f);
            for_each_var(rhs, f);
        }
        ExprKind::UnOp { expr, .. } => for_each_var(expr, f),
        ExprKind::Call { args, .. } => args.iter().for_each(|a| for_each_var(a, f)),
        ExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => {
            for_each_var(cond, f);
            for_each_var(then_expr, f);
            for_each_var(else_expr, f);
        }
        ExprKind::SetLit(elems) | ExprKind::Tuple(elems) => {
            elems.iter().for_each(|e| for_each_var(e, f));
        }
        ExprKind::Try(inner) | ExprKind::FailWith(inner) | ExprKind::KleeneStar(inner) => {
            for_each_var(inner, f);
        }
        // `var` is the comprehension's own binder, a fresh local — not a
        // reference to anything outside, so it's deliberately not visited.
        ExprKind::Comprehension {
            output,
            source,
            filter,
            ..
        } => {
            for_each_var(output, f);
            for_each_var(source, f);
            if let Some(flt) = filter {
                for_each_var(flt, f);
            }
        }
        ExprKind::Proj { base, .. } => for_each_var(base, f),
        ExprKind::Index { base, index } => {
            for_each_var(base, f);
            for_each_var(index, f);
        }
    }
}

/// For every `DefKind::Alias` name, the set of *other* `name_defs` entries
/// referenced anywhere in its value (any operator, any nesting depth).
/// `DefKind::Distinct` entries never source an edge: `set_kind` never
/// recurses into a distinct set's basis expression, so they can't
/// participate in an infinite-recursion cycle as a starting point.
fn build_raw_dep_graph(name_defs: &NameDefs) -> HashMap<Symbol, HashSet<Symbol>> {
    name_defs
        .iter()
        .filter(|(_, def)| def.kind == DefKind::Alias)
        .map(|(name, def)| {
            let mut refs = HashSet::new();
            for_each_var(&def.value, &mut |sym| {
                if name_defs.contains_key(sym) {
                    refs.insert(sym.clone());
                }
            });
            (name.clone(), refs)
        })
        .collect()
}

/// Names reachable from themselves in `raw_deps` — i.e. every name that
/// participates in at least one cycle (self-loop or longer).
fn find_cyclic_names(raw_deps: &HashMap<Symbol, HashSet<Symbol>>) -> HashSet<Symbol> {
    let mut cyclic = HashSet::new();
    for start in raw_deps.keys() {
        let mut visited: HashSet<Symbol> = HashSet::new();
        let mut stack: Vec<Symbol> = vec![start.clone()];
        let mut reaches_self = false;
        while let Some(cur) = stack.pop() {
            let Some(deps) = raw_deps.get(&cur) else {
                continue;
            };
            for d in deps {
                if d == start {
                    reaches_self = true;
                }
                if visited.insert(d.clone()) {
                    stack.push(d.clone());
                }
            }
        }
        if reaches_self {
            cyclic.insert(start.clone());
        }
    }
    cyclic
}

/// How one Cartesian-product factor (after `flatten_domain`) relates to the
/// set of names currently under well-foundedness review.
enum FactorShape {
    /// A bare `Var` reference to another name in `cyclic_names` — a
    /// recognized recursive dependency; the fixpoint below decides whether
    /// it's already known-generating.
    Dependency(Symbol),
    /// Doesn't mention any name in `cyclic_names` anywhere inside it (or is
    /// a bare `Var` to something outside that set entirely) — safe to
    /// treat as a base case.
    Base,
    /// Mentions a name in `cyclic_names` somewhere, but not as a bare
    /// top-level factor (nested under `&`, `-`, a comprehension, …) — not
    /// a shape tier 1 recognizes.
    Unrecognized,
}

fn classify_factor(factor: &Expr, cyclic_names: &HashSet<Symbol>) -> FactorShape {
    if let ExprKind::Var(sym) = &factor.kind {
        return if cyclic_names.contains(sym) {
            FactorShape::Dependency(sym.clone())
        } else {
            FactorShape::Base
        };
    }
    let mut mentions = false;
    for_each_var(factor, &mut |sym| {
        if cyclic_names.contains(sym) {
            mentions = true;
        }
    });
    if mentions {
        FactorShape::Unrecognized
    } else {
        FactorShape::Base
    }
}

/// The "generating sets" fixpoint (backlog.md): iterate until no name in
/// `cyclic_names` changes status. A name becomes `generating` once at
/// least one of its `|`-arms is built entirely from bases and/or
/// already-generating names; it becomes `unrecognized` the moment any of
/// its arms contains a factor `classify_factor` can't account for.
fn classify(
    cyclic_names: &HashSet<Symbol>,
    name_defs: &NameDefs,
) -> (HashSet<Symbol>, HashSet<Symbol>) {
    let mut generating: HashSet<Symbol> = HashSet::new();
    let mut unrecognized: HashSet<Symbol> = HashSet::new();

    loop {
        let mut changed = false;
        for name in cyclic_names {
            if generating.contains(name) || unrecognized.contains(name) {
                continue;
            }
            // Only `DefKind::Alias` names ever source an edge in
            // `build_raw_dep_graph`, so every `cyclic_names` member has a
            // real value expression here.
            let def = &name_defs[name];
            let arms = flatten_union(&def.value);

            let mut arm_is_unrecognized = false;
            let mut any_arm_generating = false;
            for arm in &arms {
                let factors = flatten_domain(arm);
                let mut all_ready = true;
                for factor in &factors {
                    match classify_factor(factor, cyclic_names) {
                        FactorShape::Base => {}
                        FactorShape::Dependency(dep) => {
                            if !generating.contains(&dep) {
                                all_ready = false;
                            }
                        }
                        FactorShape::Unrecognized => arm_is_unrecognized = true,
                    }
                }
                if all_ready {
                    any_arm_generating = true;
                }
            }

            if arm_is_unrecognized {
                unrecognized.insert(name.clone());
                changed = true;
            } else if any_arm_generating {
                generating.insert(name.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    (generating, unrecognized)
}
