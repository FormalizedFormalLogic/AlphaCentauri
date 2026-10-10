module

public import AlphaCentauri.Schemata.Induction
public import Foundation.FirstOrder.Arithmetic.IDelta.Basic

/-!
# The `Δ` induction schemes between `𝗜𝚺 n` and `𝗕𝚺(n + 1)`

A $\Delta_{n + 1}$ predicate of a model of `𝗕𝚺(n + 1)` obeys successor induction, also when it is
defined by formulas of the broad hierarchy; whether `𝗜𝚫(n + 1)` proves `𝗕𝚺(n + 1)` is open.

- [Sla04, §2.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

/-- Every model of `𝗕𝚺(n + 1)` satisfies `𝗜𝚫⁺(n + 1)`.
- [Sla04, §2.1] -/
lemma models_IDeltaOnBroadHierarchy_of_models_BSigma_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺(n + 1) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have h₀ : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n :=
    have : 𝗕𝚷 n ⪯ 𝗕𝚺 (n + 1) := CollectionOnPrenexHierarchy_weakerThan_BSigma_succ 𝚷 n
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  refine Semantics.ModelsSet.union_iff.mpr ⟨h₀, Semantics.ModelsSet.setOf_iff.mpr ?_⟩
  rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩
  apply (models_deltaInd_iff φ ψ).mpr
  intro f heq zero succ
  obtain ⟨Q, hQ, hQiff⟩ := exists_pi_definableRel_iff (Bounding.definablePred_of_hierarchy hφ f)
  obtain ⟨R, hR, hRiff⟩ := exists_pi_definableRel_iff (Bounding.definablePred_of_hierarchy hψ f)
  exact succ_induction_of_complementary_exists_pi hQ hR hQiff
    (fun x ↦ by rw [heq x, not_not]; exact hRiff x) zero succ

/-- `𝗜𝚫⁺(n + 1)` is at most as strong as `𝗕𝚺(n + 1)`.
- [Sla04, §2.1] -/
theorem IDeltaOnBroadHierarchy_weakerThan_BSigma (n : ℕ) : 𝗜𝚫⁺(n + 1) ⪯ 𝗕𝚺(n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦
    models_IDeltaOnBroadHierarchy_of_models_BSigma_succ n V

/-- `𝗕𝚺(n + 1)` is at most as strong as `𝗜𝚫(n + 1)`. This is an open problem; it holds over
`𝗜𝚺₀` extended by exponentiation.
- [HP98, Remark after Theorem I.2.5]
- [Sla04] -/
axiom BSigma_weakerThan_IDelta (n : ℕ) : 𝗕𝚺(n + 1) ⪯ 𝗜𝚫(n + 1)

end FFL.FirstOrder.Arithmetic
