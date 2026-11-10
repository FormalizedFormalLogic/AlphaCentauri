module

public import AlphaCentauri.Model.NonnegativePart
public import AlphaCentauri.Schemata.ZRing
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
theorem models_ZRing : (Nonneg (IntegerConstantPolynomial K))↓[ℒₒᵣ] ⊧* Arithmetic.ZRing := by
  apply models_theory_iff.mpr
  rintro σ (hσ | ⟨n, rfl⟩)
  · exact models_of_mem hσ
  · apply (Arithmetic.models_standardEuclideanDivisionBy_iff (n + 1)).mpr
    intro b
    obtain ⟨q, r, hr₀, hr, e⟩ := exists_eq_mul_add_of_pos (b : IntegerConstantPolynomial K)
      (n := n + 1) n.succ_pos
    have hq : 0 ≤ q := by
      by_contra h
      have := OpenPredicate.DiscretelyOrdered.one_le_of_pos (-q) (neg_pos.mpr (not_le.mp h))
      nlinarith [b.2]
    have h₁ : (⟨r, hr₀⟩ : Nonneg (IntegerConstantPolynomial K)) < ((n + 1 : ℕ) : Nonneg _) := by
      exact_mod_cast hr
    have h₂ : b = ((n + 1 : ℕ) : Nonneg _) * ⟨q, hq⟩ + ⟨r, hr₀⟩ := by
      apply Subtype.ext
      simpa using e
    use ⟨q, hq⟩, ⟨r, hr₀⟩
    let F : CommSemiring (Nonneg (IntegerConstantPolynomial K)) :=
      Arithmetic.instCommSemiring_foundation
    have hcast (m : ℕ) :
        @Nat.cast _ F.toNatCast m = (m : Nonneg (IntegerConstantPolynomial K)) := by
      induction m with
      | zero => rw [@Nat.cast_zero _ F.toAddMonoidWithOne, Nat.cast_zero]
      | succ m ih => rw [@Nat.cast_succ _ F.toAddMonoidWithOne, Nat.cast_succ, ih]
    rw [hcast]
    exact ⟨h₁, h₂⟩

end IntegerConstantPolynomial
