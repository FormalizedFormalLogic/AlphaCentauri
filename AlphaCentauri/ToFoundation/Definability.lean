module

public import Foundation.FirstOrder.Incompleteness.Definability
public import AlphaCentauri.Bootstrapping.Prenex

/-!
# The strict induction theories are `Δ₁`

The induction schema over a strict prenex class $\Sigma_s$ or $\Pi_s$ is `Δ₁`, and hence so are
the theories `𝗜𝗡𝗗 Γ s`, in particular `𝗜𝚺 s`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Theory Bootstrapping

noncomputable instance InductionScheme.delta1_strictHierarchy :
    (Γ : Polarity) → (s : ℕ) → (InductionScheme ℒₒᵣ (StrictHierarchy Γ s)).Δ₁
  | 𝚺, s =>
    { ch := chInd (isStrictSigma s)
      mem_iff φ := by
        have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] (chInd (isStrictSigma s)).val)
            ↔ InductionR (IsStrictSigma s) (⌜φ⌝ : ℕ) := by
          simp
        rw [h]
        exact (inductionR_quote_iff isStrictSigma_quote_iff_s φ).trans
          (mem_inductionScheme_iff φ).symm
      isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun _ _ _ ↦ by
        simp }
  | 𝚷, s =>
    { ch := chInd (isStrictPi s)
      mem_iff φ := by
        have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] (chInd (isStrictPi s)).val)
            ↔ InductionR (IsStrictPi s) (⌜φ⌝ : ℕ) := by
          simp
        rw [h]
        exact (inductionR_quote_iff isStrictPi_quote_iff_s φ).trans
          (mem_inductionScheme_iff φ).symm
      isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun _ _ _ ↦ by
        simp }

noncomputable instance InductionOnHierarchy.delta1 (Γ : Polarity) (s : ℕ) : (𝗜𝗡𝗗 Γ s).Δ₁ :=
  Theory.Δ₁.add PeanoMinus.delta1 inferInstance

end FFL.FirstOrder.Arithmetic
