module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILPZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.MaximalConsistentTheoryModel

/-!
# Verbrugge semantics of $\mathbf{ILP}_0$

Completeness with respect to generalised Verbrugge frames.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

variable {α : Type} {A : Formula α}

/-- - [MV20, Theorem 23] -/
theorem Logic.ILP₀.complete_verbrugge
    (h : ∀ {κ : Type} [Nonempty κ] (M : Verbrugge.Model κ α), [M.IsIL] → [M.HasP₀] → M ⊧ A) :
    𝐈𝐋𝐏₀ ⊢ A := by
  classical
  by_contra hA;
  have := Logic.ofAxioms.nonempty_countermodelWorld hA;
  have := Verbrugge.countermodel.hasP₀ (A₀ := A) fun {_ _} ↦ Logic.ILP₀.axiomP₀;
  exact Logic.ofAxioms.not_models_verbrugge_countermodel hA (h _)

end FFL.InterpretabilityLogic

end
