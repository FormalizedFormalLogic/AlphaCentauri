module

public import AlphaCentauri.InterpretabilityLogic.Veltman.StepByStepModel

/-!
# Soundness and completeness of $\mathbf{ILW}^*$

$\mathbf{ILW}^*$ proves exactly the formulas valid in the Veltman models satisfying the frame
conditions of $\mathsf{W}$ and $\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

universe u

variable {α : Type u} {A : Formula α}

/-- - [GJ08, Theorem 7.1] -/
theorem ILWStar.iff_valid :
    𝐈𝐋𝐖* ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasW] → [M.HasM₀] → M ⊧ A := by
  constructor;
  · intro h _ _ M;
    intros;
    exact ILWStar.sound h;
  · exact ILWStar.complete;

end Logic

end FFL.InterpretabilityLogic

end
