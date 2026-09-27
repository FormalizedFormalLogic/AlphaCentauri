module

public import Foundation.ProvabilityLogic.Classification.General
public import AlphaCentauri.ToFoundation.StandardProvability

/-!
# Provability logics under local reflection

If `U` proves the local $\Sigma_1$ reflection principle of `T`, the provability logic of `T`
relative to `U` has trace `ω` and contains `𝐃`. A consistent extension of `T` by a single sentence
never proves the full local reflection schema of `T`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

lemma alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) (n : ℕ) :
    alpha n ∈ T.provabilityLogicRelativeTo U (α := α) := by
  intro f
  simpa [alpha, standardInterpret, interpret, interpret_boxItr, Function.iterate_succ_apply'] using
    h ⟨_, hierarchy_iterate_standardProvability_bot n, rfl⟩

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) :
    (T.provabilityLogicRelativeTo U (α := α)).trace = .univ :=
  Set.eq_univ_of_forall fun n ↦ mem_trace_provabilityLogic_iff.mpr <|
    alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1 h n

theorem D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) :
    𝐃 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  apply sumQuasiNormal_weakerThan_provabilityLogic
  rintro _ (rfl | ⟨B, C, rfl⟩)
  · exact (A_weakerThan_provabilityLogic
      (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 h)).wk
      (Logic.A.neg_boxItr_bot (n := 1))
  · intro f
    have hσ : Hierarchy 𝚺 1 (f T (□B ⋎ □C)) := by
      simp [standardInterpret, interpret, Arithmetic.standardProvability_def]
    exact h ⟨_, hσ, rfl⟩

/-- A consistent extension of `T` by a single sentence does not prove the full local reflection
schema of `T`.
- [AB05, Theorem 23] -/
theorem not_provable_localReflectionOn_univ_insert {π : ArithmeticSentence}
    [Consistent (insert π T)] :
    ¬ insert π T ⊢* 𝗥𝗳𝗻[Set.univ] T := fun h ↦
  (T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
    (Γ := fun _ ↦ True) (fun _ _ ↦ trivial) trivial h).not_con inferInstance

end FFL.ProvabilityLogic
