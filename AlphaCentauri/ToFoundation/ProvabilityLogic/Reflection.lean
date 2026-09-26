module

public import Foundation.ProvabilityLogic.Classification.General
public import AlphaCentauri.ToFoundation.StandardProvability

/-!
# Provability logics under local reflection

If `U` proves the local $\Sigma_1$ reflection principle of `T`, the provability logic of `T`
relative to `U` has trace `ω` and contains `𝐃`.
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

end FFL.ProvabilityLogic
