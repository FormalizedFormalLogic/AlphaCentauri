module

public import AlphaCentauri.InterpretabilityLogic.Veltman.LabelledSetModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILMinus.Basic

/-!
# Soundness and completeness of $\mathbf{CL}$

$\mathbf{CL}$ proves exactly the formulas valid in the finite Veltman models satisfying the frame
conditions of $\mathbf{J1}$ and $\mathbf{J2}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

variable {α : Type} {A : Formula α}

/-- - [KO21, Theorem 5.1] -/
theorem CL.iff_valid_finite :
    𝐂𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact CL.sound h;
  · exact CL.complete;

end Logic

end FFL.InterpretabilityLogic

end
