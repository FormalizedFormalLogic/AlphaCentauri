module

public import AlphaCentauri.ToFoundation.FirstOrder.Rew
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import AlphaCentauri.ToFoundation.FirstOrder.Fvar
public import AlphaCentauri.ToFoundation.FirstOrder.BinderNotation
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.Induction.Basic

/-!
# Least witnesses of total $\Delta_1$ relations

In a model of $\mathsf{I}\Sigma_1$, choosing for each `x` the least `y` with `R x y`, for a total
$\Delta_1$ relation `R`, gives a $\Sigma_1$-definable function.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section LeastWitness

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma ISigma1.exists_sigma1Function_of_forall_exists {R : V → V → Prop} (hR : 𝚫ᴬ₁-Relation R)
    (h : ∀ x, ∃ y, R x y) : ∃ f : V → V, (𝚺ᴬ₁-Function₁ f) ∧ ∀ x, R x (f x) := by
  have hl (x : V) : ∃ y, R x y ∧ ∀ z < y, ¬R x z := by
    obtain ⟨y, hy⟩ := h x
    exact InductionOnHierarchy.least_number_sigma 𝚺 1 (P := R x) (by definability) hy
  choose f hf using hl
  use f
  constructor
  · have : 𝚺ᴬ₁-Relation fun y x : V ↦ R x y ∧ ∀ z < y, ¬R x z := by definability
    apply this.of_iff
    intro v
    change v 0 = f (v 1) ↔ R (v 1) (v 0) ∧ ∀ z < v 0, ¬R (v 1) z
    constructor
    · intro e
      rw [e]
      exact hf (v 1)
    · rintro ⟨hy, hmin⟩
      rcases lt_trichotomy (v 0) (f (v 1)) with hlt | heq | hgt
      · exact absurd hy ((hf (v 1)).2 _ hlt)
      · exact heq
      · exact absurd (hf (v 1)).1 (hmin _ hgt)
  · intro x
    exact (hf x).1

end LeastWitness

end FFL.FirstOrder.Arithmetic
