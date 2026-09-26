module

public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection
public import AlphaCentauri.ToFoundation.StandardProvability
public import Foundation.ProvabilityLogic.Classification.General

/-!
# The provability logic of `T` relative to `T + Con(U)`

If `U` extends `T` provably in `𝗜𝚺₁` and proves the local $\Sigma_1$ reflection principle of `T`,
and `T + Con(U)` is consistent, then the provability logic of `T` relative to `T + Con(U)` is `𝐀`.
In particular this holds for `T = 𝗜𝚺₁` and `U = 𝗣𝗔`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] [U.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Let `T` and `U` be theories such that `𝗜𝚺₁` proves $\mathrm{Pr}_T(\sigma) \to
\mathrm{Pr}_U(\sigma)$ for every `σ`, and `U` proves the local $\Sigma_1$ reflection principle of
`T`. If `T + Con(U)` is consistent, the provability logic of `T` relative to `T + Con(U)` is `𝐀`.
- [AB05, Example 63] -/
theorem provabilityLogic_add_con_eq_A
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) [Consistent (T ∪ U.Con)] :
    T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) = 𝐀 := by
  have : 𝗜𝚺₁ ⪯ T ∪ U.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans <|
    WeakerThan.ofSubset Set.subset_union_left
  have hT : (T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α)).trace = .univ := by
    apply Set.eq_univ_of_forall
    intro n
    apply mem_trace_provabilityLogic_iff.mpr
    intro f
    have h₁ : T ∪ U.Con ⊢ ∼U.standardProvability ⊥ := by_axm <| Set.mem_union_right _ rfl
    have h₂ := WeakerThan.pbl (𝓣 := T ∪ U.Con) <|
      provable_iterate_standardProvability_bot_imp hTU hU n
    simp only [alpha, standardInterpret, interpret, interpret_boxItr]
    cl_prover [h₁, h₂]
  rcases Logic.eq_or_strictlyWeakerThan (A_weakerThan_provabilityLogic hT) with h | h
  · exact h.symm
  obtain ⟨-, A, hAA, hA⟩ := strictlyWeakerThan_iff.mp h
  have h₁ : T ∪ U.Con ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T :=
    provable_localReflectionOn_sigma1_of_mem_of_not_A hT hA hAA
  rw [Set.union_singleton] at h₁
  have h₂ := T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
    (Γ := Hierarchy 𝚷 1) (fun _ hσ ↦ by simpa using hσ) (by simp) h₁
  rw [← Set.union_singleton] at h₂
  exact (h₂.not_con inferInstance).elim

/-- The provability logic of `𝗜𝚺₁` relative to `𝗜𝚺₁ + Con(𝗣𝗔)` is `𝐀`.
- [AB05, Example 63] -/
theorem provabilityLogic_ISigma1_add_con_Peano_eq_A :
    (𝗜𝚺₁).provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗣𝗔.Con) (α := α) = 𝐀 := by
  have : Consistent 𝗣𝗔 := Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], inferInstance⟩
  have : ℕ↓[ℒₒᵣ] ⊧* (𝗜𝚺₁ ∪ 𝗣𝗔.Con) := by
    apply Semantics.modelsSet_iff.mpr
    rintro φ (hφ | rfl)
    · exact Semantics.modelsSet_iff.mp inferInstance hφ
    · simpa [models_iff]
  have : Consistent (𝗜𝚺₁ ∪ 𝗣𝗔.Con) := Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], this⟩
  exact provabilityLogic_add_con_eq_A (ISigma.provable_standardProvability_imp_Peano 1)
    fun hσ ↦ (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔).pbl (ISigma.provable_localReflectionOn_Sigma1 le_rfl hσ)

end FFL.ProvabilityLogic
