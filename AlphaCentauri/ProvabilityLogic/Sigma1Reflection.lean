module

public import AlphaCentauri.Reflection.Sigma1Reflection
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection

/-!
# The provability logic of `T` relative to `T` plus local $\Sigma_1$ reflection

If $T + \mathrm{Rfn}_{\Sigma_1}(T)$ is consistent, the provability logic of `T` relative to it is
`𝐃`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- If $T + \mathrm{Rfn}_{\Sigma_1}(T)$ is consistent, the provability logic of `T` relative to it
is `𝐃`.
- [AB05, Example 60] -/
theorem provabilityLogic_add_localReflectionOn_Sigma1_eq_D
    [Consistent (T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T)] :
    T.provabilityLogicRelativeTo (T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) (α := α) = 𝐃 := by
  have : 𝗜𝚺₁ ⪯ T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left)
  have hR : T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T := fun hσ ↦
    by_axm <| Set.mem_union_right _ hσ
  rcases Logic.eq_or_strictlyWeakerThan
    (D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1 (α := α) hR) with h | h
  · exact h.symm
  obtain ⟨-, A, hAD, hA⟩ := strictlyWeakerThan_iff.mp h
  obtain ⟨U, _, hU, e⟩ := exists_strictPi2_axiomatization_localReflectionOn_Sigma1 (T := T)
  have hrfn : T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T ⊢* 𝗥𝗳𝗻[Hierarchy (Polarity.alt 𝚷) 2] T := by
    rintro _ ⟨σ, -, rfl⟩
    exact provable_reflection_of_not_D
      (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 hR) hA hAD
  exact ((inconsistent_of_provable_localReflectionOn_hierarchy_union (n := 1) hU e hrfn).not_con
    inferInstance).elim

/-- For a $\Sigma_1$-sound `T`, the provability logic of `T` relative to
$T + \mathrm{Rfn}_{\Sigma_1}(T)$ is `𝐃`.
- [AB05, Example 60] -/
theorem provabilityLogic_add_localReflectionOn_Sigma1_eq_D_of_sigma1Sound
    [T.SoundOnHierarchy 𝚺 1] :
    T.provabilityLogicRelativeTo (T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) (α := α) = 𝐃 :=
  have : Consistent (T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) :=
    Consistent.of_le inferInstance <| WeakerThan.ofSubset <| Set.union_subset_union_right T <|
      T.standardProvability.localReflectionOn_mono (Γ' := Set.univ) fun _ _ ↦ trivial
  provabilityLogic_add_localReflectionOn_Sigma1_eq_D

end FFL.ProvabilityLogic
