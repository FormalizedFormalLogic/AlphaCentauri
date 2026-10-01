module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import AlphaCentauri.ToFoundation.Definability

/-!
# The standard provability predicate

`𝗜𝚺₁` proves `Pr_T(σ) → Pr_U(σ)` for `T = 𝗜𝚺 m` and `U = 𝗜𝚺 n` with `m ≤ n`, and for
`T = 𝗜𝚺 m` and `U = 𝗣𝗔`.
-/

@[expose] public section

open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment Bootstrapping

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

end FFL.FirstOrder.Arithmetic
