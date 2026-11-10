module

public import AlphaCentauri.InterpretabilityLogic.Veltman.StepByStepModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZero.Basic

/-!
# Soundness and completeness of $\mathbf{ILM}_0$

$\mathbf{ILM}_0$ proves exactly the formulas valid in the Veltman models satisfying the frame
condition of $\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

variable {α : Type*} {A : Formula α}

/-- - [GJ08, Theorem 6.1] -/
theorem ILM₀.iff_valid :
    𝐈𝐋𝐌₀ ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasM₀] → M ⊧ A := by
  constructor;
  · intro h _ _ M;
    intros;
    exact ILM₀.sound h;
  · exact ILM₀.complete;

end Logic

end FFL.InterpretabilityLogic

end
