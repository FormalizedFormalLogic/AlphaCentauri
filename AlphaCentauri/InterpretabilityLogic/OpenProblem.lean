module

public import AlphaCentauri.InterpretabilityLogic.Extension
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension
public import AlphaCentauri.InterpretabilityLogic.Verbrugge.Extension

/-!
# Open problems on extensions of $\mathbf{IL}$

Whether $\mathbf{ILR}$ is complete with respect to Veltman frames, and whether $\mathbf{ILRW}$ is
complete with respect to Veltman frames or to generalised Veltman frames, are open.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

/-- $\mathbf{ILR}$ is complete with respect to Veltman frames. An open problem.
- [MV20, Section 2.5] -/
def ILRVeltmanCompletenessProblem : Prop :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsIL] [M.HasR], M ⊧ A) → 𝐈𝐋𝐑 ⊢ A

/-- $\mathbf{ILRW}$ is complete with respect to Veltman frames. An open problem.
- [JMMV20, Section 5.6.5] -/
def ILRWVeltmanCompletenessProblem : Prop :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Veltman.Model κ ℕ) [M.IsIL] [M.HasR] [M.HasW], M ⊧ A) →
      𝐈𝐋𝐑𝐖 ⊢ A

/-- $\mathbf{ILRW}$ is complete with respect to generalised Veltman frames. An open problem.
- [JMMV20, Section 5.6.5] -/
def ILRWVerbruggeCompletenessProblem : Prop :=
  ∀ A : Formula ℕ,
    (∀ (κ : Type) [Nonempty κ] (M : Verbrugge.Model κ ℕ) [M.IsIL] [M.HasR] [M.HasW], M ⊧ A) →
      𝐈𝐋𝐑𝐖 ⊢ A

end FFL.InterpretabilityLogic

end
