module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILRW.Basic
import AlphaCentauri.OpenProblem

/-!
# Open problems on the completeness of interpretability logics

Open problems on the completeness of $\mathbf{ILR}$ and $\mathbf{ILRW}$.

- [MV20, §2.5]
- [JMMV20, §6.5]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

/-- Is $\mathbf{ILR}$ complete with respect to Veltman semantics?
- [MV20, §2.5] -/
open_problem Logic.ILR.complete_veltman :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsILR], M ⊧ A) → 𝐈𝐋𝐑 ⊢ A

/-- Is $\mathbf{ILRW}$ complete with respect to Veltman semantics?
- [JMMV20, §6.5] -/
open_problem Logic.ILRW.complete_veltman :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsILRW], M ⊧ A) →
      𝐈𝐋𝐑𝐖 ⊢ A

/-- Is $\mathbf{ILRW}$ complete with respect to Verbrugge semantics?
- [JMMV20, §6.5] -/
open_problem Logic.ILRW.complete_verbrugge :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Verbrugge.Model κ ℕ) [M.IsILRW], M ⊧ A) →
      𝐈𝐋𝐑𝐖 ⊢ A

end FFL.InterpretabilityLogic
