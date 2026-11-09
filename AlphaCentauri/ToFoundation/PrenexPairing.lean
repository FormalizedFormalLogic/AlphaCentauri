module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# Prenex formulas closed under pairing
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.Prenex

open Arithmetic

variable {Γ : Polarity} {s : ℕ} {ξ : Type*} {n : ℕ}

def unpair : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 2) → ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 1)
  | _, 0, _, φ =>
    ⟨⟨“z. ∃ a <⁺ z, ∃ b <⁺ z, !(Rewriting.emb pairDef.val) z a b ∧ !φ.matrix.val a b ⋯”,
      (Hierarchy.zero_iff_bounded (Γ := 𝚺)).mp (by simp)⟩⟩
  | 𝚺, _ + 1, _, φ =>
    ((φ.sigmaInv.rew (Rew.subst (#2 :> #0 :> #1 :> (#·.succ.succ.succ)))).unpair.rew
      (Rew.subst (#1 :> #0 :> (#·.succ.succ)))).sigma
  | 𝚷, _ + 1, _, φ =>
    ((φ.piInv.rew (Rew.subst (#2 :> #0 :> #1 :> (#·.succ.succ.succ)))).unpair.rew
      (Rew.subst (#1 :> #0 :> (#·.succ.succ)))).pi

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {f : ξ → V}

lemma models_unpair (φ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 2)) (z : V) (e : Fin n → V) :
    Semiformula.Eval (z :> e) f φ.unpair.val ↔ Semiformula.Eval (π₁ z :> π₂ z :> e) f φ.val := by
  induction s generalizing Γ n z with
  | zero =>
    simp [unpair, val, Matrix.comp_vecCons, Function.comp_def]
    grind [pi₁_le_self, pi₂_le_self]
  | succ s ih =>
    rcases Γ <;> simp [unpair, ih, models_sigmaInv, models_piInv, -val_sigmaInv, -val_piInv,
      Matrix.comp_vecCons, Function.comp_def]

end models

end FFL.FirstOrder.Bounding.Prenex
