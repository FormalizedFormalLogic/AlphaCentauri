module

public import AlphaCentauri.Model.IntegerConstantDyadicPolynomial
public import AlphaCentauri.Model.OpenInduction
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Mathlib.Tactic.Ring

/-!
# Euclidean division in $\mathsf{PA}^-$

Over $\mathsf{PA}^-$, division with remainder for co-prime pairs is equivalent to division with
remainder for all pairs with a non-zero divisor. $\mathsf{PA}^-_{\mathrm{smu}}$ does not prove
either: it has a model in which every universal sentence true in `ℕ` holds and in which some
element cannot be divided by `3` with remainder.

- [Kat26b, Theorem 2, Corollary 4]
- [Kat26a, Theorem 10, Corollaries 11, 12]
- [Vis26, Open Questions 3.2, 8.29]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- Division with remainder by any non-zero divisor. -/
def euclideanDivision : ArithmeticSentence :=
  “∀ a b, a ≠ 0 → ∃ q r, r < a ∧ b = a * q + r”

/-- Division with remainder for co-prime pairs. -/
def coprimeEuclideanDivision : ArithmeticSentence :=
  “∀ a b, (∃ c d, a * d = b * c + 1) → ∃ q r, r < a ∧ b = a * q + r”

noncomputable section

open Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {s t x y : V}

/-- - [Kat26b, Theorem 2] -/
lemma exists_div_of_exists_div_mul_add (hs : s < t)
    (h : ∃ q r, r < t * x ∧ t * y + s = t * x * q + r) : ∃ q r, r < x ∧ y = x * q + r := by
  rcases h with ⟨q, u, hu, e⟩
  have hxq : x * q ≤ y := by
    by_contra hlt
    have h₁ : t * (y + 1) ≤ t * (x * q) := mul_le_mul_left (lt_iff_succ_le.mp (not_le.mp hlt))
    have h₂ : t * (x * q) ≤ t * y + s := by rw [← mul_assoc, e]; exact le_self_add
    have h₃ : t * y + t ≤ t * y + s := by simpa [mul_add] using h₁.trans h₂
    exact absurd (le_of_add_le_add_left h₃) (not_le.mpr hs)
  obtain ⟨r, hr⟩ := exists_add_of_le hxq
  use q, r
  and_intros
  · by_contra hxr
    have h₁ : t * (x * q) + (t * r + s) = t * (x * q) + u := by
      rw [← add_assoc, ← mul_add, ← hr, e, mul_assoc]
    have h₂ : t * x ≤ u := (mul_le_mul_left (not_lt.mp hxr)).trans
      (le_self_add.trans (add_left_cancel h₁).le)
    exact absurd hu (not_lt.mpr h₂)
  · exact hr

/-- - [Kat26b, Corollary 3] -/
lemma exists_coprime_sq_mul_add_one (hx : 1 < x) (hy : 0 < y) :
    ∃ c d, x * x * d = (x * y + 1) * c + 1 := by
  obtain ⟨z, hz⟩ := exists_add_of_le (pos_iff_one_le.mp (mul_pos (zero_lt_one.trans hx) hy))
  use z, y * y
  calc x * x * (y * y) = (x * y) * (x * y) := by ring
    _ = (1 + z) * (1 + z) := by rw [← hz]
    _ = (1 + z + 1) * z + 1 := by ring
    _ = _ := by rw [← hz]

lemma models_coprimeEuclideanDivision_iff_models_euclideanDivision :
    V↓[ℒₒᵣ] ⊧ coprimeEuclideanDivision ↔ V↓[ℒₒᵣ] ⊧ euclideanDivision := by
  suffices (∀ a b c d : V, a * d = b * c + 1 → ∃ q r, r < a ∧ b = a * q + r) ↔
      ∀ a b : V, a ≠ 0 → ∃ q r, r < a ∧ b = a * q + r by
    simpa [models_iff, coprimeEuclideanDivision, euclideanDivision] using this
  constructor
  · intro H x y hx
    rcases eq_or_ne y 0 with rfl | hy
    · use 0, 0
      and_intros <;> simp [pos_iff_ne_zero.mpr hx]
    rcases eq_or_ne x 1 with rfl | hx1
    · use y, 0
      simp
    have hx1 : 1 < x := lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hx)) hx1.symm
    obtain ⟨c, d, h⟩ := exists_coprime_sq_mul_add_one hx1 (pos_iff_ne_zero.mpr hy)
    obtain ⟨q, r, hr, e⟩ := H (x * x) (x * y + 1) c d h
    apply exists_div_of_exists_div_mul_add (s := 1) (t := x) hx1
    use q, r
  · intro H a b c d h
    apply H a b
    rintro rfl
    simp at h

end

/-- - [Kat26b, Corollary 4] -/
theorem coprimeEuclideanDivision_iff_euclideanDivision :
    𝗣𝗔⁻ ⊢ coprimeEuclideanDivision 🡘 euclideanDivision :=
  complete.{0} _ _ fun (V : Type) _ _ ↦ by
    simpa using models_coprimeEuclideanDivision_iff_models_euclideanDivision (V := V)

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder

open IntegerConstantDyadicPolynomial

/-- There is a model of $\mathsf{PA}^-_{\mathrm{smu}}$ in which every universal sentence true in
`ℕ` holds and in which some element cannot be divided by `3` with remainder.
- [Kat26a, Theorem 10] -/
theorem exists_model_PeanoMinusSmu_not_standardEuclideanDivisionBy_three :
    ∃ (M : Type) (_ : ORingStructure M), M↓[ℒₒᵣ] ⊧* Arithmetic.PeanoMinusSmu ∧
      (∀ φ : ArithmeticSemiformula ℕ 0, φ.Open → ℕ↓[ℒₒᵣ] ⊧ φ.univCl → M↓[ℒₒᵣ] ⊧ φ.univCl) ∧
      ¬M↓[ℒₒᵣ] ⊧ Arithmetic.standardEuclideanDivisionBy 3 := by
  use Nonneg IntegerConstantDyadicPolynomial, inferInstance
  and_intros
  · exact models_PeanoMinusSmu
  · intro _ hφ h
    exact IntegerConstantDyadicPolynomial.models_univCl_of_open hφ h
  · exact not_models_standardEuclideanDivisionBy_three

/-- $\mathsf{PA}^-_{\mathrm{smu}}$ does not prove division with remainder by `3`.
- [Kat26a, Corollary 11] -/
theorem not_provable_standardEuclideanDivisionBy_three_PeanoMinusSmu :
    Arithmetic.PeanoMinusSmu ⊬ Arithmetic.standardEuclideanDivisionBy 3 := by
  intro h
  exact not_models_standardEuclideanDivisionBy_three <| models_of_provable models_PeanoMinusSmu h

/-- $\mathsf{PA}^-_{\mathrm{smu}}$ does not prove the Euclidean Division Principle.
- [Kat26a, Corollary 12]
- [Vis26, Open Question 3.2] -/
theorem not_provable_euclideanDivision_PeanoMinusSmu :
    Arithmetic.PeanoMinusSmu ⊬ Arithmetic.euclideanDivision := by
  intro h
  have h : ∀ a b : Nonneg IntegerConstantDyadicPolynomial, a ≠ 0 →
      ∃ q r, r < a ∧ b = a * q + r := by
    simpa [models_iff, Arithmetic.euclideanDivision] using models_of_provable models_PeanoMinusSmu h
  apply not_models_standardEuclideanDivisionBy_three
  rw [Arithmetic.models_standardEuclideanDivisionBy_iff, Nonneg.natCast_foundation]
  intro b
  exact h 3 b three_ne_zero

end FFL.FirstOrder
