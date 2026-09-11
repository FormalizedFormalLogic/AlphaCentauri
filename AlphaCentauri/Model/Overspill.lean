module

public import AlphaCentauri.Model.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-! # Overspill

In a proper end extension satisfying induction for a hierarchy class, a formula of that class
which holds at every element of the base model holds below some element outside the base model.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula

variable {M N : Type u} [ORingStructure M] [hMN : M ⊂ₑ N]

/-- Overspill: a formula of the induction class holding at every element of the base model holds
below some element outside it.
- [HP98, Corollary IV.1.16]
- [vO99, Lemma 3.2, Corollary 3.3] -/
theorem overspill (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : Hierarchy Γ m φ) (e : ℕ → N)
    (h : ∀ a : M, φ.Eval ![hMN.emb a] e) :
    ∃ c : N, c ∉ Set.range hMN.emb ∧ ∀ x < c, φ.Eval ![x] e := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m)
  by_contra! hc
  have h₁ : ∀ x : N, (∀ y < x, φ.Eval ![y] e) → x ∈ Set.range hMN.emb := by grind;
  have h₂ : ∀ x : N, (∀ y < x, φ.Eval ![y] e) → ∀ y < x + 1, φ.Eval ![y] e := by
    intro x ih y hy;
    obtain ⟨a, rfl⟩ := h₁ x ih;
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hy) with hy' | rfl
    · exact ih y hy'
    · exact h a
  have h₃ : ∀ x : N, ∀ y < x, φ.Eval ![y] e :=
    InductionScheme.succ_induction (C := Hierarchy Γ m)
      ⟨e, (φ/[#0]).ballLT #0, by simp [hφ], fun x ↦ by simp [eval_ballLT]⟩
      (by simp) h₂
  exact hMN.not_surjective fun x ↦ h₁ x (h₃ x)

end FFL.FirstOrder.Arithmetic
