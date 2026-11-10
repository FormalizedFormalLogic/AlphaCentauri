module

public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModelM

/-!
# Soundness and completeness of $\mathbf{ILM}$

$\mathbf{ILM}$ proves exactly the formulas valid in the finite Veltman models satisfying the frame
condition of $\mathsf{M}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

universe u

variable {α : Type u} {A : Formula α}

/-- - [dJV90, Theorem 6.3] -/
theorem ILM.iff_valid_finite :
    𝐈𝐋𝐌 ⊢ A ↔ ∀ {κ : Type u} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasM] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILM.sound h;
  · exact ILM.complete;

end Logic

end FFL.InterpretabilityLogic

end
