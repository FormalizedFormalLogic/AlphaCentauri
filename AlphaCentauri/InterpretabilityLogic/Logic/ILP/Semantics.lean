module

public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedBranchModel
public import AlphaCentauri.InterpretabilityLogic.Logic.ILP.Basic

/-!
# Soundness and completeness of $\mathbf{ILP}$

$\mathbf{ILP}$ proves exactly the formulas valid in the finite Veltman models satisfying the frame
condition of $\mathsf{P}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

variable {α : Type} {A : Formula α}

/-- - [dJV90, Theorem 5.2] -/
theorem ILP.iff_valid_finite :
    𝐈𝐋𝐏 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsIL] → [M.HasP] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M;
    intros;
    exact ILP.sound h;
  · exact ILP.complete;

end Logic

end FFL.InterpretabilityLogic

end
