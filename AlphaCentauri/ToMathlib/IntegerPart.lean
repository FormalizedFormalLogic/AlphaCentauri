module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Shepherdson's criterion for open induction

A discretely ordered ring satisfies open induction if and only if it is an integer part of the
real closure of its fraction field.
-/

@[expose] public section

namespace OpenPredicate

/-- Shepherdson's criterion: a discretely ordered ring `R` satisfies open induction if and only if
it is an integer part of the real closure `K` of its fraction field, that is, every `α : K` has
some `r : R` with `r ≤ α < r + 1`. The real closure is given as a real closed field algebraic over
`R` into which `R` embeds as an ordered ring.
- [She64]
- [BO96, Theorem 1.1]
- [GG17, Theorem 1] -/
axiom openInduction_iff_integerPart {R K : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [DiscretelyOrdered R] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [IsRealClosed K] [Algebra R K] [Algebra.IsAlgebraic R K]
    (hmono : StrictMono (algebraMap R K)) :
    OpenInduction R ↔ ∀ α : K, ∃ r : R, algebraMap R K r ≤ α ∧ α < algebraMap R K r + 1

end OpenPredicate
