module

public import AlphaCentauri.Model.EndExtension
public import Foundation.FirstOrder.Arithmetic.Schemata

/-! # Overspill

In a proper end extension satisfying induction for a hierarchy class, a formula of that class
which holds at every element of the base model holds below some element outside the base model.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


open Semiformula

universe u v

variable {M : Type u} {N : Type v} [ORingStructure M] [ORingStructure N] (e : M ⊂ₑ N)

/-- Overspill: a formula of the induction class holding at every element of the base model holds
below some element outside it.
- [HP98, Corollary IV.1.16]
- [vO99, Lemma 3.2, Corollary 3.3] -/
theorem overspill (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ m φ) (f : ℕ → N)
    (h : ∀ a : M, φ.Eval ![e a] f) :
    ∃ c : N, c ∉ Set.range e.emb ∧ ∀ x < c, φ.Eval ![x] f := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m)
  by_contra! hc
  have h₁ : ∀ x : N, (∀ y < x, φ.Eval ![y] f) → x ∈ Set.range e.emb := by grind;
  have h₂ : ∀ x : N, (∀ y < x, φ.Eval ![y] f) → ∀ y < x + 1, φ.Eval ![y] f := by
    intro x ih y hy;
    obtain ⟨a, rfl⟩ := h₁ x ih;
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hy) with hy' | rfl
    · exact ih y hy'
    · exact h a
  have h₃ : ∀ x : N, ∀ y < x, φ.Eval ![y] f :=
    InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy Γ m)
      ⟨f, (φ/[#0]).ballLT #0, by simp [hφ], fun x ↦ by simp [eval_ballLT]⟩
      (by simp) h₂
  exact e.not_surjective fun x ↦ h₁ x (h₃ x)


end FFL.FirstOrder.Arithmetic
