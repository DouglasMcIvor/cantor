//! Membership predicates for *named* sets — split from `membership.rs` to
//! keep that file under 1000 lines.
//!
//! This is exactly the `SemExprKind::Var(sym)` arm of `membership_constraint`
//! (builtins like `Int`, `Nat`, `Bool`, `Char`, `Rational`,
//! `Signed32`/`Unsigned32`, `Fail`, `None`, plus user `alias`/`distinct`
//! names) together with the integer-bound helpers only that arm needs — no
//! other match arm in `membership_constraint` touches `IntBound`/`to_int`
//! reasoning at all, so the cut here is a real seam, not an arbitrary one.

use cvc5::{Kind, Term, TermManager};

use crate::ast::DefKind;
use crate::kind::Kind as ValKind;
use crate::semantics::builtins::{self, FloatBound, IntBound};
use crate::span::Symbol;

use super::NameDefs;
use super::membership::{Membership, SolverPreds, membership_constraint};

/// Pass through a cvc5 term only if it's already integer-sorted, for use in
/// arithmetic membership constraints against scalar (integer-valued) sets.
///
/// Bool and Int are disjoint in Cantor's value model — a boolean-sorted term
/// is never a member of `Int`/`Nat`/`NonZeroInt`/etc., the same as a tuple or
/// any other non-integer sort. Callers should return `Constrained(false)`
/// when this returns `None`.
fn to_integer_term<'tm>(t: Term<'tm>) -> Option<Term<'tm>> {
    if t.sort().is_integer() { Some(t) } else { None }
}

/// The integer reading of `t` for a bound check against an `Int` subset, plus
/// the side condition that makes that reading faithful.
///
/// - Integer-sorted `t`: itself, no side condition.
/// - Real-sorted `t` (a `Rational`): `to_int(t)` paired with `is_int(t)`.
///   SMT-LIB's `to_int` is *floor*, so it only agrees with `t` once `is_int(t)`
///   holds — which is exactly why the guard is returned alongside rather than
///   left to the caller to remember. This is the whole numeric tower in one
///   function: narrowing ℚ to ℤ is a proof obligation, never a truncation.
/// - Anything else (bool, tuple, a distinct sort): `None`, and callers return
///   `Constrained(false)` — not a member.
fn integer_reading<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
) -> Option<(Term<'tm>, Option<Term<'tm>>)> {
    if t.sort().is_integer() {
        Some((t, None))
    } else if t.sort().is_real() {
        let guard = is_integer_pred(tm, &t);
        Some((tm.mk_term(Kind::ToInteger, &[t]), Some(guard)))
    } else {
        None
    }
}

/// "`t` is a whole number", for a real-sorted `t`.
///
/// The obvious encoding is `is_int(t)`, and that is what this falls back to.
/// But when `t` is literally `(/ a b)` over two *integer*-sorted operands —
/// overwhelmingly the common case, since every `a / b` on `Int`s has that
/// shape — it instead emits the equivalent integer-arithmetic statement
/// `(= (mod a b) 0)`.
///
/// This is not a micro-optimisation. cvc5's `nl-cov` (libpoly CAD) engine,
/// which `configured_solver` enables to stop the *integer* `x * x` bounds
/// check from hanging (docs/design-decisions.md, 2026-07-05), does not
/// terminate on `is_int` over a nonlinear real division — and `tlimit` is
/// ignored, so it hangs rather than reporting `Unknown`. The two engines turn
/// out to be complementary: whichever one is selected globally, the other's
/// query shape hangs. Restating divisibility in integer arithmetic sidesteps
/// the choice entirely, keeping `nl-cov` on and both query shapes fast
/// (measured: 1.5ms sat / 0.5ms unsat, versus a non-terminating `is_int`).
///
/// `mod` is SMT-LIB's Euclidean remainder, which is zero exactly when `b`
/// divides `a`, for either sign — so this is an equivalence, not an
/// approximation. A zero divisor is excluded separately and unconditionally
/// by `/`'s own `NonZeroRational` obligation, so the `b = 0` corner (where
/// both `mod` and `/` are underspecified) is never reachable in a query that
/// gets this far.
fn is_integer_pred<'tm>(tm: &'tm TermManager, t: &Term<'tm>) -> Term<'tm> {
    if t.kind() == Kind::Division && t.num_children() == 2 {
        let (a, b) = (t.child(0), t.child(1));
        if a.sort().is_integer() && b.sort().is_integer() {
            let m = tm.mk_term(Kind::IntsModulus, &[a, b]);
            return tm.mk_term(Kind::Equal, &[m, tm.mk_integer(0)]);
        }
    }
    tm.mk_term(Kind::IsInteger, std::slice::from_ref(t))
}

/// Conjoin an optional `is_int` side condition onto a bound predicate.
fn with_guard<'tm>(
    tm: &'tm TermManager,
    guard: Option<Term<'tm>>,
    pred: Term<'tm>,
) -> Membership<'tm> {
    Membership::Constrained(match guard {
        Some(g) => tm.mk_term(Kind::And, &[g, pred]),
        None => pred,
    })
}

/// The additive identity at `t`'s own sort — cvc5 auto-coerces `Int` into
/// `Real` for arithmetic and ordering, but *not* for `Equal`/`Distinct`,
/// where a mixed pair is a fatal C++-level sort error rather than a catchable
/// one. `NonZeroInt`/`NonZeroRational` both go through `Distinct`, so they
/// need the literal built at the matching sort.
fn zero_like<'tm>(tm: &'tm TermManager, t: &Term<'tm>) -> Term<'tm> {
    if t.sort().is_real() {
        tm.mk_real(0)
    } else {
        tm.mk_integer(0)
    }
}

pub(crate) fn bounded<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    min: i64,
    max: i64,
) -> Membership<'tm> {
    let Some(t) = to_integer_term(t) else {
        return Membership::Constrained(tm.mk_boolean(false));
    };
    let lo = tm.mk_integer(min);
    let hi = tm.mk_integer(max);
    let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
    let leq = tm.mk_term(Kind::Leq, &[t, hi]);
    Membership::Constrained(tm.mk_term(Kind::And, &[geq, leq]))
}

/// The complement of [`bounded`]: `t < min || t > max` — currently only
/// reached via `BigInt = Int - Int64` (`Outside(i64::MIN, i64::MAX)`).
fn outside<'tm>(tm: &'tm TermManager, t: Term<'tm>, min: i64, max: i64) -> Membership<'tm> {
    let Some(t) = to_integer_term(t) else {
        return Membership::Constrained(tm.mk_boolean(false));
    };
    let lo = tm.mk_integer(min);
    let hi = tm.mk_integer(max);
    let lt = tm.mk_term(Kind::Lt, &[t.clone(), lo]);
    let gt = tm.mk_term(Kind::Gt, &[t, hi]);
    Membership::Constrained(tm.mk_term(Kind::Or, &[lt, gt]))
}

/// The basis obligation for `char(n)` (`solver::encode_call`): `n` is a valid
/// Unicode scalar value iff `0 <= n <= 0x10FFFF` and `n` isn't a surrogate
/// (`0xD800..=0xDFFF`). `t` here is the plain-`Int` argument term, *not* yet
/// wrapped in `mk_Char` — this is the same "check the raw basis value before
/// constructing" shape as `litre(n)`'s obligation
/// (`encode_call.rs::distinct_def_for_constructor`), just with a hardcoded
/// predicate instead of a `membership_constraint` over a user set expression
/// (there's no Cantor-expressible basis set for this yet — no range-literal
/// syntax exists).
pub(crate) fn unicode_scalar_valid<'tm>(tm: &'tm TermManager, t: Term<'tm>) -> Membership<'tm> {
    let Some(t) = to_integer_term(t) else {
        return Membership::Constrained(tm.mk_boolean(false));
    };
    let in_range = {
        let lo = tm.mk_integer(0);
        let hi = tm.mk_integer(0x10FFFF);
        let geq = tm.mk_term(Kind::Geq, &[t.clone(), lo]);
        let leq = tm.mk_term(Kind::Leq, &[t.clone(), hi]);
        tm.mk_term(Kind::And, &[geq, leq])
    };
    let not_surrogate = {
        let lo = tm.mk_integer(0xD800);
        let hi = tm.mk_integer(0xDFFF);
        let lt = tm.mk_term(Kind::Lt, &[t.clone(), lo]);
        let gt = tm.mk_term(Kind::Gt, &[t, hi]);
        tm.mk_term(Kind::Or, &[lt, gt])
    };
    Membership::Constrained(tm.mk_term(Kind::And, &[in_range, not_surrogate]))
}

/// Membership against a named set: a builtin (`Int`/`Nat`/`Bool`/`Char`/
/// `Rational`/`Signed32`/`Unsigned32`/`Fail`/`None`/…) or a user-defined
/// `alias`/`distinct` name. Called from `membership_constraint`'s
/// `SemExprKind::Var(sym)` arm.
pub(crate) fn membership_constraint_for_named<'tm>(
    tm: &'tm TermManager,
    t: Term<'tm>,
    sym: &Symbol,
    name_defs: &NameDefs,
    distinct_preds: &SolverPreds<'tm>,
) -> Membership<'tm> {
    match builtins::lookup(&sym.0) {
        // `Fail` is registered as a builtin distinct sort (`build_distinct_preds`)
        // with a single witness value — a term of exactly that sort is
        // trivially a member; anything else (integer, boolean, another
        // distinct sort, tuple, …) is definitely not `Fail`. Same rule as
        // any user `distinct` set (the `DefKind::Distinct` arm below);
        // `Fail` is just resolved via `builtins::lookup` instead of
        // `name_defs` since it's a language builtin, not a user definition.
        Some(b) if b.kind == ValKind::Fail => {
            let fail_sort = distinct_preds
                .get(&Symbol::new("Fail"))
                .expect("Fail must be registered as a builtin distinct sort")
                .sort
                .clone();
            if t.sort() == fail_sort {
                Membership::Unconstrained
            } else {
                Membership::Constrained(tm.mk_boolean(false))
            }
        }
        // `None` is registered as a builtin distinct sort too
        // (`build_distinct_preds`), same rule as `Fail` above — a term of
        // exactly that sort is trivially a member; anything else is not.
        Some(b) if b.kind == ValKind::None => {
            let none_sort = distinct_preds
                .get(&Symbol::new("None"))
                .expect("None must be registered as a builtin distinct sort")
                .sort
                .clone();
            if t.sort() == none_sort {
                Membership::Unconstrained
            } else {
                Membership::Constrained(tm.mk_boolean(false))
            }
        }
        // `Char` is registered as a builtin distinct sort too (`build_distinct_preds`),
        // same rule as `Fail` above — a term of exactly the `Char` sort is
        // trivially a member (validity was already proved once, at
        // `char(n)` construction — see `encode_call.rs`); anything else
        // is definitely not `Char`.
        Some(b) if b.kind == ValKind::Char => {
            let char_sort = distinct_preds
                .get(&Symbol::new("Char"))
                .expect("Char must be registered as a builtin distinct sort")
                .sort
                .clone();
            if t.sort() == char_sort {
                Membership::Unconstrained
            } else {
                Membership::Constrained(tm.mk_boolean(false))
            }
        }
        // Bool = {0, 1} (false = 0, true = 1).
        // • boolean-sort terms are trivially in Bool — no constraint needed.
        // • integer-sort terms (e.g. from a Bool|Nat domain) need t = 0 OR t = 1.
        // Checking the term's sort avoids creating arithmetic constraints on
        // boolean-sort terms, which would cause a fatal CVC5 sort error.
        Some(b) if b.kind == ValKind::Bool => {
            if t.sort().is_boolean() {
                Membership::Unconstrained
            } else {
                // Use to_integer_term so that tuple-sort terms correctly
                // resolve to Constrained(false) — a tuple is never in Bool.
                match to_integer_term(t) {
                    None => Membership::Constrained(tm.mk_boolean(false)),
                    Some(t_int) => {
                        let eq0 = tm.mk_term(Kind::Equal, &[t_int.clone(), tm.mk_integer(0)]);
                        let eq1 = tm.mk_term(Kind::Equal, &[t_int, tm.mk_integer(1)]);
                        Membership::Constrained(tm.mk_term(Kind::Or, &[eq0, eq1]))
                    }
                }
            }
        }
        // `Signed32`/`Unsigned32` (docs/wrapping-and-quotient-sets-
        // plan.md): each is its own opaque CVC5 sort, same rule as
        // `Fail`/`distinct` above — a term of exactly that sort is
        // trivially a member, anything else (Int, the other wrapping
        // sort, a distinct sort, tuple, …) is definitely not.
        Some(b) if b.kind == ValKind::Signed32 || b.kind == ValKind::Unsigned32 => {
            let info = distinct_preds
                .wrapping
                .get(sym)
                .expect("Signed32/Unsigned32 must be registered as builtin wrapping sorts");
            if t.sort() == info.d_sort {
                Membership::Unconstrained
            } else {
                Membership::Constrained(tm.mk_boolean(false))
            }
        }
        // `Rational` / `NonZeroRational` — the one builtin family that is
        // a *superset* of `Int`. Both an integer- and a real-sorted term
        // is a member (ℤ ⊂ ℚ); every other sort is not. Only `Any` and
        // `NonZero` are reachable, since those are the only two ℚ-Kinded
        // builtins — the rest of `IntBound` has no ℚ analogue in v0 (see
        // docs/rational-plan.md open question 2) and says so loudly.
        Some(b) if b.kind == ValKind::Rational => {
            if !t.sort().is_real() && !t.sort().is_integer() {
                return Membership::Constrained(tm.mk_boolean(false));
            }
            match b.bound {
                IntBound::Any => Membership::Unconstrained,
                IntBound::NonZero => {
                    let zero = zero_like(tm, &t);
                    Membership::Constrained(tm.mk_term(Kind::Distinct, &[t, zero]))
                }
                IntBound::NonNeg | IntBound::Positive => Membership::Unsupported,
                IntBound::Bounded(..) | IntBound::Outside(..) => Membership::Unsupported,
            }
        }
        // `Float32`/`FiniteFloat32` — a genuine cvc5 FloatingPoint sort
        // (`sort::scalar_kind_sort`), same "own sort ⇒ trivially a member"
        // rule as `Char`/`Signed32` above for plain `Float32`.
        // `FiniteFloat32` additionally excludes `±infinity32`/`nan32` — a
        // value-range refinement of the same sort (mirrors `Nat`⊆`Int`
        // being a bound on the same integer sort), not a second opaque
        // sort, so this is the one builtin family whose bound lives in
        // `FloatBound` rather than `IntBound`.
        Some(b) if b.kind == ValKind::Float32 => {
            if !t.sort().is_fp() {
                return Membership::Constrained(tm.mk_boolean(false));
            }
            match b.float_bound {
                FloatBound::Any => Membership::Unconstrained,
                FloatBound::Finite => {
                    let is_inf = tm.mk_term(Kind::FloatingpointIsInf, std::slice::from_ref(&t));
                    let is_nan = tm.mk_term(Kind::FloatingpointIsNan, &[t]);
                    let not_finite = tm.mk_term(Kind::Or, &[is_inf, is_nan]);
                    Membership::Constrained(tm.mk_term(Kind::Not, &[not_finite]))
                }
            }
        }
        // `Int` and its named integer subsets (Nat, NatPos, NonZeroInt,
        // Int8…Int64) all resolve to an integer-sort membership predicate
        // parameterised by `IntBound` — which name means which bound is
        // decided once, centrally, in `semantics::builtins`.
        //
        // A *real*-sorted term reaching here is the numeric tower's
        // headline case: `f : Int -> Int` with a `/` body asks the solver
        // to discharge a divisibility theorem, not to truncate. See
        // `integer_reading`.
        Some(b) => {
            if b.bound == IntBound::Any {
                // Integer sort is the only sort in plain `Int`.  A term of
                // distinct sort, boolean sort, or tuple sort is NOT in Int.
                if t.sort().is_integer() {
                    Membership::Unconstrained
                } else if t.sort().is_real() {
                    Membership::Constrained(is_integer_pred(tm, &t))
                } else {
                    Membership::Constrained(tm.mk_boolean(false))
                }
            } else {
                let Some((t, guard)) = integer_reading(tm, t) else {
                    return Membership::Constrained(tm.mk_boolean(false));
                };
                let zero = tm.mk_integer(0);
                match b.bound {
                    IntBound::NonNeg => with_guard(tm, guard, tm.mk_term(Kind::Geq, &[t, zero])),
                    IntBound::Positive => with_guard(tm, guard, tm.mk_term(Kind::Gt, &[t, zero])),
                    IntBound::NonZero => {
                        with_guard(tm, guard, tm.mk_term(Kind::Distinct, &[t, zero]))
                    }
                    IntBound::Bounded(min, max) => match bounded(tm, t, min, max) {
                        Membership::Constrained(p) => with_guard(tm, guard, p),
                        other => other,
                    },
                    IntBound::Outside(min, max) => match outside(tm, t, min, max) {
                        Membership::Constrained(p) => with_guard(tm, guard, p),
                        other => other,
                    },
                    IntBound::Any => unreachable!(),
                }
            }
        }
        None => {
            // Check user-defined set definitions.
            if let Some(def) = name_defs.get(sym) {
                // Expanding an alias is the one step here that leaves the
                // expression tree for another definition, so it's the one
                // step a definition cycle can spin forever on. Panics
                // rather than returning (no `CompileError` in this
                // function's signature) — still far better than the stack
                // overflow it replaces. See src/recursion.rs.
                let _guard = crate::recursion::enter_definition_or_panic(&sym.0);
                match def.kind {
                    // Alias: transparent — expand to the RHS set expression.
                    DefKind::Alias => {
                        membership_constraint(tm, t, &def.value, name_defs, distinct_preds)
                    }
                    // Distinct: compare the term's CVC5 sort against the set's
                    // uninterpreted sort.  A value of the right sort is trivially
                    // a member; any other sort (integer, bool, another distinct
                    // sort, …) is definitely not a member.
                    DefKind::Distinct => {
                        if let Some(info) = distinct_preds.get(sym) {
                            if t.sort() == info.sort {
                                Membership::Unconstrained // right sort → trivially in the set
                            } else {
                                Membership::Constrained(tm.mk_boolean(false)) // wrong sort → never in the set
                            }
                        } else {
                            Membership::Unsupported
                        }
                    }
                }
            } else {
                Membership::Unsupported
            }
        }
    }
}
