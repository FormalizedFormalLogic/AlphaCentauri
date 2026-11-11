module

public import AlphaCentauri.Axiomatizability.ISigma.Finite
public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection
public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.ProvabilityLogic.Classification.Truth

/-!
# Provability logic of $\mathsf{I}\Sigma_n$ relative to $\mathsf{PA}$

For $n \ge 1$, the provability logic of $\mathsf{I}\Sigma_n$ relative to $\mathsf{PA}$ is
$\mathbf{S}$.

- [AB05, Example 61]
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
  set L := (𝗜𝚺n).provabilityLogicRelativeTo 𝗣𝗔;
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  apply Logic.weakerThan_antisymm;
  · suffices L ⪯ (𝗜𝚺n).provabilityLogicRelativeTo 𝗧𝗔 by
      rwa [Logic.S.eq_provabilityLogicRelativeTo_TA (T := 𝗜𝚺 n)];
    constructor;
    intro A hA f;
    exact (inferInstance : 𝗣𝗔 ⪯ 𝗧𝗔).pbl (hA f);
  · exact S_weakerThan_provabilityLogic_of_provable_localReflection
      <| Peano.provable_localReflection_ISigma n
end FFL.ProvabilityLogic
