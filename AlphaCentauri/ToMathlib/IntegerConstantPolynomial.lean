module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The $\mathbb{Z}$-ring of polynomials with integer constant term

For an ordered field `K`, the polynomials over `K` whose constant term is an integer form a subring
`IntegerConstantPolynomial K` of `K[X]`. Ordered by the sign of the leading coefficient, it is a
discretely ordered ring in which `X` is greater than every natural number, and every element can be
divided with remainder by every positive natural number.
-/

@[expose] public noncomputable section

open Polynomial OpenPredicate

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
lemma Polynomial.leadingCoeff_add_nonneg {p q : K[X]} (hp : 0 ≤ p.leadingCoeff)
    (hq : 0 ≤ q.leadingCoeff) : 0 ≤ (p + q).leadingCoeff := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · rwa [leadingCoeff_add_of_degree_lt h]
  · by_cases hpq : p.leadingCoeff + q.leadingCoeff = 0
    · obtain rfl : p = 0 := leadingCoeff_eq_zero.mp (by linarith)
      simpa using hq
    · rw [leadingCoeff_add_of_degree_eq h hpq]
      exact add_nonneg hp hq
  · rwa [leadingCoeff_add_of_degree_lt' h]

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

/-- The polynomials with non-negative leading coefficient. -/
def cone : RingCone (IntegerConstantPolynomial K) where
  carrier := {p | 0 ≤ (p : K[X]).leadingCoeff}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := Polynomial.leadingCoeff_add_nonneg
  mul_mem' hp hq := by simpa [leadingCoeff_mul] using mul_nonneg hp hq
  eq_zero_of_mem_of_neg_mem' {p} hp hnp := by
    have : (p : K[X]).leadingCoeff = 0 := le_antisymm (by simpa using hnp) hp
    exact Subtype.ext (leadingCoeff_eq_zero.mp this)

instance : HasMemOrNegMem (cone : RingCone (IntegerConstantPolynomial K)) where
  mem_or_neg_mem p := by
    rcases le_total 0 (p : K[X]).leadingCoeff with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [cone] using h)

open Classical in
instance : LinearOrder (IntegerConstantPolynomial K) :=
  LinearOrder.mkOfAddGroupCone cone

instance : IsStrictOrderedRing (IntegerConstantPolynomial K) :=
  haveI : IsOrderedRing (IntegerConstantPolynomial K) := IsOrderedRing.mkOfCone cone
  inferInstance

variable {p q : IntegerConstantPolynomial K}

lemma le_iff : p ≤ q ↔ 0 ≤ ((q - p : IntegerConstantPolynomial K) : K[X]).leadingCoeff := Iff.rfl

lemma nonneg_iff : 0 ≤ p ↔ 0 ≤ (p : K[X]).leadingCoeff := by simp [le_iff]

lemma pos_iff : 0 < p ↔ 0 < (p : K[X]).leadingCoeff := by
  simp [lt_iff_le_and_ne, nonneg_iff, eq_comm (a := (0 : K)),
    eq_comm (a := (0 : IntegerConstantPolynomial K))]

instance : DiscretelyOrdered (IntegerConstantPolynomial K) where
  one_le_of_pos p hp := by
    rw [pos_iff] at hp
    rw [← sub_nonneg, nonneg_iff]
    by_cases h : (p : K[X]).natDegree = 0
    · obtain ⟨n, hn⟩ := mem_iff.mp p.2
      have hlc : (p : K[X]).leadingCoeff = n := by rw [leadingCoeff, h, hn]
      rw [hlc] at hp
      have : (0 : ℤ) < n := by exact_mod_cast hp
      have : (p : K[X]) - 1 = C ((n - 1 : ℤ) : K) := by
        conv_lhs => rw [eq_C_of_natDegree_eq_zero h, hn]
        simp
      rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, this, leadingCoeff_C]
      exact_mod_cast sub_nonneg.mpr (by omega : (1 : ℤ) ≤ n)
    · rw [AddSubgroupClass.coe_sub, sub_eq_add_neg, leadingCoeff_add_of_degree_lt']
      · exact hp.le
      · simpa using natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero h)

lemma natCast_lt_X (n : ℕ) : (n : IntegerConstantPolynomial K) < X K := by
  rw [← sub_pos, pos_iff]
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
    rw [nonneg_iff, hr, leadingCoeff_C]
    exact_mod_cast Int.emod_nonneg m (b := n) (by exact_mod_cast hn.ne')
  have h₂ : r < n := by
    rw [← sub_pos, pos_iff, AddSubgroupClass.coe_sub, hn_coe, hr, ← C_sub, leadingCoeff_C]
    exact_mod_cast sub_pos.mpr (Int.emod_lt_of_pos m (by exact_mod_cast hn))
  have h₃ : a = n * q + r := by
    apply Subtype.ext
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, hn_coe, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hn']
    simp [hr]
  use q, r

end IntegerConstantPolynomial
