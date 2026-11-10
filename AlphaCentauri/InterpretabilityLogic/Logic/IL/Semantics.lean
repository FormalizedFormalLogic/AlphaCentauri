module

public import AlphaCentauri.InterpretabilityLogic.Veltman.IndexedSetModel
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# Soundness and completeness of $\mathbf{IL}$

$\mathbf{IL}$ proves exactly the formulas valid in the finite Veltman models, equivalently in the
finite generalised Veltman models, equivalently in the finite $\mathbf{IL}^-$-models satisfying the
frame conditions of $\mathbf{J1}$, $\mathbf{J2}$ and $\mathbf{J5}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

namespace Logic

open Veltman.Model.World

variable {α : Type} {A : Formula α}

/-- - [dJV90, Theorem 4.1]
- [JMMV20, Theorem 3.2]
-/
theorem IL.semantics_TFAE : [
    𝐈𝐋 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Verbrugge.Model κ α), [M.IsIL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 3 := by
    intro h _ _ _ M _;
    exact ofAxioms.sound_verbrugge (by simp) h;
  tfae_have 3 → 2 := by
    intro h _ _ _ M _ x;
    exact Veltman.Model.forces_toVerbrugge.mp (h M.toVerbrugge x);
  tfae_have 2 → 1 := IL.complete;
  tfae_finish;

/-- - [KO21, Theorem 5.4] -/
theorem IL.iff_valid_finite_ILMinus :
    𝐈𝐋 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsILMinus] → [M.IsJ1] → [M.IsJ2] → [M.IsJ5] → M ⊧ A := by
  constructor;
  · intro h _ _ _ M _ _ _ _;
    have : M.IsIL := .of_isILMinus;
    exact ofAxioms.sound (by simp) h;
  · exact IL.complete_ILMinus;

end Logic

end FFL.InterpretabilityLogic

end
