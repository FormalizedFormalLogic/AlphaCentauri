module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# The intermediate value property of real closed fields
-/

@[expose] public section

open Polynomial

/-- A polynomial over a real closed ordered field that changes sign on an interval has a root
inside it.
- [BCR98, §1.2] -/
axiom IsRealClosed.exists_mem_Ioo_isRoot {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] {f : R[X]} {a b : R} (hab : a < b)
    (ha : f.eval a < 0) (hb : 0 < f.eval b) : ∃ c ∈ Set.Ioo a b, f.IsRoot c
