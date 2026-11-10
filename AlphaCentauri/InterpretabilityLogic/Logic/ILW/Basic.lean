module

public import AlphaCentauri.InterpretabilityLogic.Veltman.RankedSetModel

/-!
# Soundness and completeness of $\mathbf{ILW}$

$\mathbf{ILW}$ proves exactly the formulas valid in the finite Veltman models satisfying the frame
condition of $\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

universe u

variable {α : Type u} {A : Formula α}

/-- - [dJV99, Theorem 13] -/
theorem ILW.iff_valid_finite :
    𝐈𝐋𝐖 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasW] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILW.sound h;
  · exact ILW.complete;

end Logic

end FFL.InterpretabilityLogic

end
