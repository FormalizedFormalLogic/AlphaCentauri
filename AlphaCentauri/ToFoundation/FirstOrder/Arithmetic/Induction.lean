module

public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.Induction.Basic

/-!
# Induction and collection schemata

Supplements `Foundation.FirstOrder.Arithmetic.Schemata` and
`Foundation.FirstOrder.Arithmetic.Induction`: rewriting an induction axiom, reading a collection
axiom in a model of `𝗣𝗔⁻`, and least witnesses of total $\Delta_1$ relations in a model of
$\mathsf{I}\Sigma_1$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section Schemata

open Rewriting LawfulSyntacticRewriting

variable {L : Language} [L.ORing]

lemma rew_succInd (ω : SyntacticRew L 0 0) (φ : Semiformula L ℕ 1) :
    ω ▹ succInd φ = succInd (ω.q ▹ φ) := by
  have h₀ : ω ▹ (φ/[((0 : ℕ) : Semiterm L ℕ 0)]) = (ω.q ▹ φ)/[((0 : ℕ) : Semiterm L ℕ 0)] := by
    rw [Rew.app_substs]
    simp
  have h₁ : ω.q ▹ (φ/[‘(#0 + 1)’]) = (ω.q ▹ φ)/[‘(#0 + 1)’] := by
    simpa [← TransitiveRewriting.comp_app] using Rewriting.smul_ext' <| by
      ext x
      · cases x using Fin.cases with
        | zero => simp [Rew.comp_app]
        | succ i => exact i.elim0
      · simp [Rew.comp_app]
  simp [succInd, h₀, h₁]

/-- The reading of the collection axiom in a structure.
- [HP98, §I.2(a)] -/
lemma models_collectionAxiom_iff {V : Type*} [ORingStructure V]
    (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] f) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f := by
  simp [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs]

end Schemata

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
