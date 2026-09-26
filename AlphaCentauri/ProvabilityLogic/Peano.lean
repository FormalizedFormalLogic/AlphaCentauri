module

public import AlphaCentauri.Reflection.Peano
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection
public import Foundation.ProvabilityLogic.Classification.Truth

/-!
# The provability logic of `𝗜𝚺 n` relative to `𝗣𝗔`

For `n ≥ 1`, the provability logic of `𝗜𝚺 n` relative to `𝗣𝗔` is `𝐒`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {n : ℕ}

/-- For $n \ge 1$, the provability logic of $\mathsf{I}\Sigma_n$ relative to $\mathsf{PA}$ is
$\mathbf{S}$.
- [AB05, Example 61] -/
theorem provabilityLogic_ISigma_Peano_eq_S (hn : 1 ≤ n) :
    (𝗜𝚺 n).provabilityLogicRelativeTo 𝗣𝗔 (α := α) = 𝐒 := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  have h₁ : (𝗜𝚺 n).provabilityLogicRelativeTo 𝗣𝗔 (α := α) ⪯
      (𝗜𝚺 n).provabilityLogicRelativeTo 𝗧𝗔 :=
    ⟨fun _ hA f ↦ (inferInstance : 𝗣𝗔 ⪯ 𝗧𝗔).pbl (hA f)⟩
  apply Logic.weakerThan_antisymm
  · exact Logic.S.eq_provabilityLogicRelativeTo_TA (T := 𝗜𝚺 n) ▸ h₁
  · exact S_weakerThan_provabilityLogic_of_provable_localReflection <|
      Peano.provable_localReflection_ISigma n

end FFL.ProvabilityLogic
