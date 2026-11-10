module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILR.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.MaximalConsistentTheoryModel

/-!
# Verbrugge semantics of $\mathbf{ILR}$

Completeness with respect to generalised Verbrugge frames.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

variable {α : Type} {A : Formula α}

/-- - [MV20, Theorem 25] -/
theorem Logic.ILR.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α), [M.IsIL] → [M.HasR] → M ⊧ A) :
    𝐈𝐋𝐑 ⊢ A := by
  classical
  by_contra hA;
  have := Logic.ofAxioms.nonempty_countermodelWorld hA;
  have := Verbrugge.countermodel.hasR (A₀ := A) fun {_ _ _} ↦ Logic.ILR.axiomR;
  exact Logic.ofAxioms.not_models_verbrugge_countermodel hA (h _)

end FFL.InterpretabilityLogic

end
