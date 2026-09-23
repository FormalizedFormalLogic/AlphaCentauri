module

public import AlphaCentauri.ToFoundation.Rew
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Rewriting an induction axiom, and reading a collection axiom

The induction axiom of a formula is built from it by substitution and quantification, so a
rewriting passes through it; the collection axiom of a formula reads in a model of `𝗣𝗔⁻` as the
statement that witnesses below a bound admit a common bound.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

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

/-- The reading of the collection axiom in a model of `𝗣𝗔⁻`.
- [HP98, §I.2(a)] -/
lemma models_collectionAxiom_iff {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] f) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f := by
  simp [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs]

end FFL.FirstOrder.Arithmetic

end
