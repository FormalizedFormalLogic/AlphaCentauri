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
  have hmn' : 𝗜𝚺 m ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hmn.le
  have hR : 𝗜𝚺 n ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] (𝗜𝚺 m) := fun hσ ↦
    (ISigma_weakerThan_of_le hmn).pbl (ISigma.provable_localReflectionOn_Sigma1 hm hσ)
  rcases Logic.eq_or_strictlyWeakerThan
    (D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1 (α := α) hR) with h | h
  · exact h.symm
  obtain ⟨-, A, hAD, hA⟩ := strictlyWeakerThan_iff.mp h
  obtain ⟨π, hπ⟩ := ISigma.exists_pi_axiomatization n (by omega)
  have h₁ : 𝗜𝚺 n ⪯ insert π.val (𝗜𝚺 m) :=
    hπ.symm.le.trans <| WeakerThan.ofSubset <| Set.singleton_subset_iff.mpr <| Set.mem_insert _ _
  have h₂ : insert π.val (𝗜𝚺 m) ⪯ 𝗜𝚺 n := WeakerThan.ofAxm! <| by
    rintro φ (rfl | hφ)
    · exact hπ.le.pbl <| by_axm rfl
    · exact hmn'.pbl <| by_axm hφ
  have h₃ : insert π.val (𝗜𝚺 m) ⊢* 𝗥𝗳𝗻[Set.univ] (𝗜𝚺 m) := by
    rintro _ ⟨σ, -, rfl⟩
    exact h₁.pbl <| provable_reflection_of_not_D
      (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 hR) hA hAD
  have h₄ := (𝗜𝚺 m).standardProvability.inconsistent_of_provable_localReflectionOn_insert
    (Γ := fun _ ↦ True) (fun _ _ ↦ trivial) trivial h₃
  have : Consistent (𝗜𝚺 n) := Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], inferInstance⟩
  exact ((h₄.of_ge h₂).not_con inferInstance).elim

end FFL.ProvabilityLogic
