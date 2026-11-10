module

public import AlphaCentauri.ToMathlib.OpenPredicate
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Subrings of polynomials ordered by the leading coefficient

For an ordered field `K`, every subring `S` of `K[X]` is ordered by the sign of the leading
coefficient, so that `X` is greater than every constant. The order is a scoped instance in
`Polynomial.LeadingCoeffOrder`; it is discrete when every constant polynomial in `S` is an integer.
-/

@[expose] public noncomputable section

open OpenPredicate

namespace Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma leadingCoeff_add_nonneg {p q : K[X]} (hp : 0 ≤ p.leadingCoeff)
    (hq : 0 ≤ q.leadingCoeff) : 0 ≤ (p + q).leadingCoeff := by
  rcases lt_trichotomy p.degree q.degree with h | h | h
  · rwa [leadingCoeff_add_of_degree_lt h]
  · by_cases hpq : p.leadingCoeff + q.leadingCoeff = 0
    · obtain rfl : p = 0 := leadingCoeff_eq_zero.mp (by linarith)
      simpa using hq
    · rw [leadingCoeff_add_of_degree_eq h hpq]
      exact add_nonneg hp hq
  · rwa [leadingCoeff_add_of_degree_lt' h]

/-- The polynomials in `S` with non-negative leading coefficient. -/
def leadingCoeffCone (S : Subring K[X]) : RingCone S where
  carrier := {p | 0 ≤ (p : K[X]).leadingCoeff}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := leadingCoeff_add_nonneg
  mul_mem' hp hq := by simpa [leadingCoeff_mul] using mul_nonneg hp hq
  eq_zero_of_mem_of_neg_mem' {p} hp hnp := by
    have : (p : K[X]).leadingCoeff = 0 := le_antisymm (by simpa using hnp) hp
    exact Subtype.ext (leadingCoeff_eq_zero.mp this)

instance (S : Subring K[X]) : HasMemOrNegMem (leadingCoeffCone S) where
  mem_or_neg_mem p := by
    rcases le_total 0 (p : K[X]).leadingCoeff with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [leadingCoeffCone] using h)

namespace LeadingCoeffOrder

variable {S : Subring K[X]}

open Classical in
scoped instance : LinearOrder S := LinearOrder.mkOfAddGroupCone (leadingCoeffCone S)

scoped instance : IsStrictOrderedRing S :=
  haveI : IsOrderedRing S := IsOrderedRing.mkOfCone (leadingCoeffCone S)
  inferInstance

variable {p q : S}

lemma le_iff : p ≤ q ↔ 0 ≤ ((q - p : S) : K[X]).leadingCoeff := Iff.rfl

lemma nonneg_iff : 0 ≤ p ↔ 0 ≤ (p : K[X]).leadingCoeff := by simp [le_iff]

lemma pos_iff : 0 < p ↔ 0 < (p : K[X]).leadingCoeff := by
  simp [lt_iff_le_and_ne, nonneg_iff, eq_comm (a := (0 : K)), eq_comm (a := (0 : S))]

/-- `S` is discretely ordered when each of its constant polynomials is an integer. -/
lemma discretelyOrdered (h : ∀ p ∈ S, p.natDegree = 0 → ∃ n : ℤ, p = n) : DiscretelyOrdered S where
  one_le_of_pos p hp := by
    rw [pos_iff] at hp
    rw [← sub_nonneg, nonneg_iff, AddSubgroupClass.coe_sub, OneMemClass.coe_one]
    by_cases hd : (p : K[X]).natDegree = 0
    · obtain ⟨n, hn⟩ := h p p.2 hd
      rw [hn, ← C_eq_intCast, leadingCoeff_C] at hp
      rw [hn, ← C_eq_intCast, ← C_1, ← C_sub, leadingCoeff_C]
      have : (0 : ℤ) < n := by exact_mod_cast hp
      exact_mod_cast sub_nonneg.mpr (by omega : (1 : ℤ) ≤ n)
    · rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt']
      · exact hp.le
      · simpa using natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)

end LeadingCoeffOrder

end Polynomial
