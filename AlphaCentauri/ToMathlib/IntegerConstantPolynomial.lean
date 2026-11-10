module

public import AlphaCentauri.ToMathlib.LeadingCoeffOrder

/-!
# The $\mathbb{Z}$-ring of polynomials with integer constant term

For an ordered field `K`, the polynomials over `K` whose constant term is an integer form a subring
`IntegerConstantPolynomial K` of `K[X]`. Ordered by the sign of the leading coefficient, it is a
discretely ordered ring in which `X` is greater than every natural number, and every element can be
divided with remainder by every positive natural number.
-/

@[expose] public noncomputable section

open Polynomial OpenPredicate

/-- The polynomials over `K` whose constant term is an integer.
- [DAq05, §2]
- [Raf10, Introduction] -/
def IntegerConstantPolynomial (K : Type*) [Field K] : Subring K[X] :=
  (Int.castRingHom K).range.comap constantCoeff

namespace IntegerConstantPolynomial

variable {K : Type*} [Field K]

lemma mem_iff {p : K[X]} : p ∈ IntegerConstantPolynomial K ↔ ∃ n : ℤ, p.coeff 0 = n := by
  simp [IntegerConstantPolynomial, eq_comm]

variable (K) in
def X : IntegerConstantPolynomial K := ⟨Polynomial.X, mem_iff.mpr ⟨0, by simp⟩⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

open scoped LeadingCoeffOrder

instance : LinearOrder (IntegerConstantPolynomial K) := inferInstance

instance : IsStrictOrderedRing (IntegerConstantPolynomial K) := inferInstance

instance : DiscretelyOrdered (IntegerConstantPolynomial K) :=
  LeadingCoeffOrder.discretelyOrdered fun p hp hd ↦ by
    obtain ⟨n, hn⟩ := mem_iff.mp hp
    use n
    rw [eq_C_of_natDegree_eq_zero hd, hn, C_eq_intCast]

lemma natCast_lt_X (n : ℕ) : (n : IntegerConstantPolynomial K) < X K := by
  rw [← sub_pos, LeadingCoeffOrder.pos_iff]
  simp [IntegerConstantPolynomial.X, ← C_eq_natCast, -map_natCast]

lemma exists_eq_mul_add_of_pos (a : IntegerConstantPolynomial K) {n : ℕ} (hn : 0 < n) :
    ∃ q r : IntegerConstantPolynomial K, 0 ≤ r ∧ r < n ∧ a = n * q + r := by
  obtain ⟨m, hm⟩ := mem_iff.mp a.2
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hmod : ((m % n : ℤ) : K) + n * ((m / n : ℤ) : K) = m := by
    exact_mod_cast Int.emod_add_mul_ediv m n
  let r : IntegerConstantPolynomial K := ⟨C ((m % n : ℤ) : K), mem_iff.mpr ⟨m % n, by simp⟩⟩
  have hq : (C (n : K)⁻¹ * ((a : K[X]) - r)).coeff 0 = ((m / n : ℤ) : K) := by
    have : (m : K) - ((m % n : ℤ) : K) = n * ((m / n : ℤ) : K) := by linarith
    simp only [coeff_C_mul, coeff_sub, hm, r, coeff_C_zero]
    rw [this, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  let q : IntegerConstantPolynomial K := ⟨_, mem_iff.mpr ⟨m / n, hq⟩⟩
  have hr : (r : K[X]) = C ((m % n : ℤ) : K) := rfl
  have hn_coe : ((n : IntegerConstantPolynomial K) : K[X]) = C (n : K) := by simp
  have h₁ : 0 ≤ r := by
    rw [LeadingCoeffOrder.nonneg_iff, hr, leadingCoeff_C]
    exact_mod_cast Int.emod_nonneg m (b := n) (by exact_mod_cast hn.ne')
  have h₂ : r < n := by
    rw [← sub_pos, LeadingCoeffOrder.pos_iff, AddSubgroupClass.coe_sub, hn_coe, hr, ← C_sub,
      leadingCoeff_C]
    exact_mod_cast sub_pos.mpr (Int.emod_lt_of_pos m (by exact_mod_cast hn))
  have h₃ : a = n * q + r := by
    apply Subtype.ext
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, hn_coe, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hn']
    simp [hr]
  use q, r

end IntegerConstantPolynomial
