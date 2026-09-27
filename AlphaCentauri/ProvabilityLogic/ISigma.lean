module

public import AlphaCentauri.Axiomatizability.ISigma
public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection
public import Foundation.ProvabilityLogic.Classification.General

/-!
# The provability logic of `𝗜𝚺 m` relative to `𝗜𝚺 n`

For `1 ≤ m < n`, the provability logic of `𝗜𝚺 m` relative to `𝗜𝚺 n` is `𝐃`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {m n : ℕ}

/-- For $1 \le m < n$, the provability logic of $\mathsf{I}\Sigma_m$ relative to
$\mathsf{I}\Sigma_n$ is $\mathbf{D}$.
- [AB05, Example 62] -/
theorem provabilityLogic_ISigma_ISigma_eq_D (hm : 1 ≤ m) (hmn : m < n) :
    (𝗜𝚺 m).provabilityLogicRelativeTo (𝗜𝚺 n) (α := α) = 𝐃 := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 m := ISigma_weakerThan_of_le hm
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le (by omega)
  -- (i) `𝗜𝚺 n` proves the local `Σ₁` reflection principle of `𝗜𝚺 m`.
  have hR : 𝗜𝚺 n ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] (𝗜𝚺 m) := fun hσ ↦
    (ISigma_weakerThan_of_le hmn).pbl (ISigma.provable_localReflectionOn_Sigma1 hm hσ)
  -- (ii) `𝐃` is weaker than the provability logic.
  have hD := D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1 (α := α) hR
  refine Logic.weakerThan_antisymm ?_ hD
  -- (iii) a strictly stronger logic would force `𝗜𝚺 n` to yield full local reflection of `𝗜𝚺 m`
  -- from a single extra axiom, contradicting `ℕ ⊧ 𝗜𝚺 n`.
  by_contra h
  obtain ⟨-, A, hAD, hA⟩ := strictlyWeakerThan_iff.mp
    (⟨hD, h⟩ : 𝐃 ⪱ (𝗜𝚺 m).provabilityLogicRelativeTo (𝗜𝚺 n) (α := α))
  obtain ⟨π, hπ⟩ := ISigma.exists_pi_axiomatization_insert n (by omega) m hmn.le
  have : Consistent (insert π.val (𝗜𝚺 m)) :=
    (Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], inferInstance⟩ : Consistent (𝗜𝚺 n)).of_le
      hπ.symm.le
  exact not_provable_localReflectionOn_univ_insert (T := 𝗜𝚺 m) (π := π.val) <| by
    rintro _ ⟨σ, -, rfl⟩
    exact hπ.le.pbl <| provable_reflection_of_not_D
      (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 hR) hA hAD

end FFL.ProvabilityLogic
