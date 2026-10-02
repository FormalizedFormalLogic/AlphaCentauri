module

public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# The standard provability predicate

`𝗜𝚺₁` proves `Pr_T(σ) → Pr_U(σ)` for `T` the induction over the prenex class $\Gamma_s$ and `U`
the induction over the broad class of the same level.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment Bootstrapping

lemma Bootstrapping.IsPrenexHierarchy.isHierarchy {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {Γ : Polarity} {n : ℕ} {p : V} (h : IsPrenexHierarchy Γ n p) :
    IsHierarchy Γ n p := by
  induction n generalizing Γ p with
  | zero => exact h
  | succ n ih =>
    obtain ⟨q, rfl, hq⟩ := h
    exact IsHierarchy.quant (IsHierarchy.of_alt (ih hq))

theorem InductionOnPrenexHierarchy.provable_standardProvability_imp_InductionOnHierarchy
    (Γ : Polarity) (s : ℕ) (σ : ArithmeticSentence) :
    𝗜𝚺₁ ⊢ (𝗜𝗡𝗗 Γ s).standardProvability σ 🡒 (𝗜𝗡𝗗⁺ Γ s).standardProvability σ :=
  provable_standardProvability_imp_of_Δ₁Class_subset (fun _ _ _ _ hp ↦
    InductionOnHierarchy.mem_Δ₁Class_iff.mpr <| (mem_Δ₁Class_iff.mp hp).imp_right <|
      InductionR.mono fun _ ↦ IsPrenexHierarchy.isHierarchy) σ

end FFL.FirstOrder.Arithmetic
