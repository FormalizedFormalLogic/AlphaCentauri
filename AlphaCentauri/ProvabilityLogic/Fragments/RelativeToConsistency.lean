module

public import AlphaCentauri.Axiomatizability.ISigma.Finite
public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection
public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.ProvabilityLogic.Classification.Truth

/-!
# Provability logic of $\mathsf{I}\Sigma_1$ over $\mathsf{I}\Sigma_1 + \mathrm{Con}(\mathsf{PA})$

The provability logic of $\mathsf{I}\Sigma_1$ relative to
$\mathsf{I}\Sigma_1 + \mathrm{Con}(\mathsf{PA})$ is $\mathbf{A}$.

- [AB05, Example 63]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*}

/-- The provability logic of `𝗜𝚺₁` relative to `𝗜𝚺₁ + Con(𝗣𝗔)` is `𝐀`.
- [AB05, Example 63] -/
theorem provabilityLogic_ISigma1_add_con_Peano_eq_A :
    (𝗜𝚺₁).provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗣𝗔.Con) (α := α) = 𝐀 := by
  apply provabilityLogic_add_con_eq_A;
  · exact InductionOnPrenexHierarchy.provable_standardProvability_imp_Peano 1;
  · intro σ hσ;
    exact (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔).pbl (ISigma.provable_localReflectionOn_Sigma1 le_rfl hσ)
  · apply Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], ?_⟩;
    apply Semantics.modelsSet_iff.mpr;
    rintro φ (hφ | rfl)
    · exact Semantics.modelsSet_iff.mp inferInstance hφ
    · simp [models_iff]

end FFL.ProvabilityLogic
