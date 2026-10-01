module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions

/-!
# Existence of a prime factor
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

lemma exists_isPrime_dvd {n : V} (h : 1 < n) : ∃ p, IsPrime p ∧ p ∣ n := by
  obtain ⟨p, ⟨hp1, hpn⟩, hmin⟩ :=
    ISigma0.least_number (P := fun d ↦ 1 < d ∧ d ∣ n) (by definability) ⟨h, dvd_refl n⟩
  refine ⟨p, ⟨hp1, ?_⟩, hpn⟩
  intro b hbp hbd
  by_contra hcon
  push Not at hcon
  obtain ⟨hb1, hbp'⟩ := hcon
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hbd
    simp [hbd] at hp1
  have hb1' : 1 < b := lt_of_le_of_ne (one_le_of_zero_lt b (pos_iff_ne_zero.mpr hb0)) (Ne.symm hb1)
  exact hmin b (lt_of_le_of_ne hbp hbp') ⟨hb1', hbd.trans hpn⟩

end FFL.FirstOrder.Arithmetic
