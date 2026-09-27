module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import AlphaCentauri.ToFoundation.Definability
public import Foundation.FirstOrder.Incompleteness.Reflection.Local

/-!
# The standard provability predicate

If every model of `𝗜𝚺₁` sees the axioms of `T` among those of `U`, then `𝗜𝚺₁` proves
`Pr_T(σ) → Pr_U(σ)`. This applies to `𝗜𝚺 m` and `𝗜𝚺 n` for `m ≤ n`, and to `𝗜𝚺 m` and `𝗣𝗔`.

If `U` proves the local $\Sigma_1$ reflection principle of `T`, then `U` refutes every iterate
`Pr_T^n(⊥)`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment Bootstrapping

variable {T U : ArithmeticTheory} [T.Δ₁] [U.Δ₁]

theorem provable_standardProvability_imp_of_Δ₁Class_subset
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V), p ∈ T.Δ₁Class → p ∈ U.Δ₁Class)
    (σ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, standardProvability_def] using
      fun hp ↦ (hp.toDerivable.of_ss (h V)).toProvable

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma InductionR.mono {S S' : V → Prop} (hS : ∀ K, S K → S' K) {p : V} (h : InductionR S p) :
    InductionR S' p := by
  obtain ⟨m, hm, b, hb, hp, hU, hsh, hbv, K, hK, hKs, hKS, hsub⟩ := h
  exact ⟨m, hm, b, hb, hp, hU, hsh, hbv, K, hK, hKs, hS K hKS, hsub⟩

lemma mem_Δ₁Class_ISigma_iff {m : ℕ} {p : V} :
    p ∈ (𝗜𝚺 m).Δ₁Class ↔ p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class ∨ InductionR (IsStrictSigma m) p := by
  change V ⊧/![p] (PeanoMinus.delta1.ch ⋎ chInd (isStrictSigma m)).val ↔ _
  simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq]
  exact Iff.or Iff.rfl (by simp)

lemma mem_Δ₁Class_Peano_iff {p : V} :
    p ∈ 𝗣𝗔.Δ₁Class ↔ p ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class ∨ InductionR (fun _ ↦ True) p := by
  change V ⊧/![p] (PeanoMinus.delta1.ch ⋎ chUniv).val ↔ _
  simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq]
  exact Iff.or Iff.rfl (by simp)

end

variable {m n : ℕ}

theorem ISigma.provable_standardProvability_imp_of_le (h : m ≤ n) (σ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ (𝗜𝚺 m).standardProvability σ 🡒 (𝗜𝚺 n).standardProvability σ :=
  provable_standardProvability_imp_of_Δ₁Class_subset (fun _ _ _ _ hp ↦
    mem_Δ₁Class_ISigma_iff.mpr <| (mem_Δ₁Class_ISigma_iff.mp hp).imp id <|
      InductionR.mono fun _ ↦ IsStrictSigma.mono h) σ

theorem ISigma.provable_standardProvability_imp_Peano (m : ℕ) (σ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ (𝗜𝚺 m).standardProvability σ 🡒 𝗣𝗔.standardProvability σ :=
  provable_standardProvability_imp_of_Δ₁Class_subset (fun _ _ _ _ hp ↦
    mem_Δ₁Class_Peano_iff.mpr <| (mem_Δ₁Class_ISigma_iff.mp hp).imp id <|
      InductionR.mono fun _ _ ↦ trivial) σ

section Iterate

variable {T U : ArithmeticTheory} [T.Δ₁]

lemma hierarchy_iterate_standardProvability_bot (n : ℕ) :
    Hierarchy 𝚺 1 (T.standardProvability^[n] ⊥) := by
  rcases n with _ | n <;> simp [Function.iterate_succ_apply', standardProvability_def]

lemma provable_neg_iterate_standardProvability_bot (hU : U ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) :
    ∀ n, U ⊢ ∼T.standardProvability^[n] ⊥
  | 0 => by simp
  | n + 1 => by
    have h₁ : U ⊢ T.standardProvability.refl (T.standardProvability^[n] ⊥) :=
      hU ⟨_, hierarchy_iterate_standardProvability_bot n, rfl⟩
    have h₂ := provable_neg_iterate_standardProvability_bot hU n
    rw [Function.iterate_succ_apply']
    cl_prover [h₁, h₂]

variable [U.Δ₁]

lemma provable_iterate_standardProvability_bot_imp
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T) (n : ℕ) :
    𝗜𝚺₁ ⊢ T.standardProvability^[n + 1] ⊥ 🡒 U.standardProvability ⊥ := by
  have h₀ := provable_neg_iterate_standardProvability_bot hU n
  rw [Function.iterate_succ_apply']
  generalize T.standardProvability^[n] ⊥ = σ at h₀ ⊢
  have h₁ : U ⊢ σ 🡒 ⊥ := by cl_prover [h₀]
  exact C_trans (hTU σ) (U.standardProvability.D2 ⨀ U.standardProvability.D1 h₁)

end Iterate

end FFL.FirstOrder.Arithmetic
