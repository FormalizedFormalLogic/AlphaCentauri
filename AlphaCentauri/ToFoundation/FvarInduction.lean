module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Structural induction on one-variable formulas with free-variable instances

Structural induction on one-variable semiformulas in which the quantifier case instantiates the
inner bound variable with a free variable depending on the quantified formula.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma isSemitermVec_fvar_bvar (u : V) : IsSemitermVec L 2 1 (?[^&u, ^#(0 : V)] : V) :=
  IsSemitermVec.adjoin (IsSemitermVec.adjoin (IsSemitermVec.nil _) (by simp)) (by simp)

/-- Structural induction on one-variable formulas whose quantifier case instantiates the inner
bound variable with the free variable `^&(g (^∀ p))`. -/
lemma IsSemiformula.sigma1_induction_fvar {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    {g : V → V} (hg : 𝚺ᴬ₁-Function₁ g)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p →
      P (Bootstrapping.subst L ?[^&(g (^∀ p)), ^#(0 : V)] p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p →
      P (Bootstrapping.subst L ?[^&(g (^∃ p)), ^#(0 : V)] p) → P (^∃ p))
    {p : V} : IsSemiformula L 1 p → P p := by
  have hm : 𝚺ᴬ₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (Bootstrapping.subst L ?[^&(g p), ^#(0 : V)] (π₂ (p - 1)))
  have hf : 𝚺ᴬ₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp)
          (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have hw : IsSemitermVec L 2 1 (?[^&(g (^∀ p₁)), ^#(0 : V)] : V) :=
      isSemitermVec_fvar_bvar _
    have h₂ : IsSemiformula L 1 (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁) :=
      h₁.subst hw
    have : P (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁) :=
      ih (Bootstrapping.subst L ?[^&(g (^∀ p₁)), ^#(0 : V)] p₁)
        (by simp only [le_sup_iff, f]; right; simp [qqAll])
        (by simp [fomulaComplexity_substs h₁ hw, h₁.isUFormula]) h₂
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have hw : IsSemitermVec L 2 1 (?[^&(g (^∃ p₁)), ^#(0 : V)] : V) :=
      isSemitermVec_fvar_bvar _
    have h₂ : IsSemiformula L 1 (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁) :=
      h₁.subst hw
    have : P (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁) :=
      ih (Bootstrapping.subst L ?[^&(g (^∃ p₁)), ^#(0 : V)] p₁)
        (by simp only [le_sup_iff, f]; right; simp [qqExs])
        (by simp [fomulaComplexity_substs h₁ hw, h₁.isUFormula]) h₂
    exact hexs _ h₁ this

end FFL.FirstOrder.Arithmetic.Bootstrapping
