module

public import AlphaCentauri.ToFoundation.Rew
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Rewriting an induction axiom

The induction axiom of a formula is built from it by substitution and quantification, so a
rewriting passes through it.
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

end FFL.FirstOrder.Arithmetic

end
