module

public import AlphaCentauri.Model.NonnegativePart
public import AlphaCentauri.ToMathlib.IntegerConstantPolynomial

/-!
# The non-negative part of the $\mathbb{Z}$-ring of polynomials with integer constant term

For an ordered field `K`, the non-negative part of `IntegerConstantPolynomial K` is a model of
$\mathsf{ZR}$ in which `X` is a nonstandard element.
-/

@[expose] public section

open FFL FirstOrder Polynomial

namespace IntegerConstantPolynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The non-negative part of `IntegerConstantPolynomial K` is a model of $\mathsf{ZR}$.
- [DAq05, §2]
- [Raf10, Introduction] -/
theorem models_ZRing : (Nonneg (IntegerConstantPolynomial K))↓[ℒₒᵣ] ⊧* Arithmetic.ZRing :=
  Nonneg.models_ZRing exists_eq_mul_add_of_pos

end IntegerConstantPolynomial
