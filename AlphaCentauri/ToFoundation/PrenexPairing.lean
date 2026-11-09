module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# Prenex formulas closed under pairing
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {P : V → Prop}

lemma exists_iff_exists_pair : (∃ z, P z) ↔ ∃ x y, P ⟪x, y⟫ :=
  ⟨fun ⟨z, h⟩ ↦ ⟨π₁ z, π₂ z, by simpa using h⟩, fun ⟨x, y, h⟩ ↦ ⟨⟪x, y⟫, h⟩⟩

lemma forall_iff_forall_pair : (∀ z, P z) ↔ ∀ x y, P ⟪x, y⟫ :=
  ⟨fun h x y ↦ h ⟪x, y⟫, fun h z ↦ by simpa using h (π₁ z) (π₂ z)⟩

end FFL.FirstOrder.Arithmetic

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

def exsPair (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n :=
  φ.sigmaInv.unpair.sigma

def allPair (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ n :=
  φ.piInv.unpair.pi

def andPair : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => ⟨⟨_, .and φ.matrix.bounded ψ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, φ, ψ =>
    (andPair (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))
      (ψ.sigmaInv.rew (Rew.subst (#1 :> (#·.succ.succ))))).unpair.sigma
  | 𝚷, _ + 1, _, φ, ψ => (andPair φ.piInv ψ.piInv).pi

def orPair : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => ⟨⟨_, .or φ.matrix.bounded ψ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, φ, ψ => (orPair φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ =>
    (orPair (φ.piInv.rew (Rew.subst (#0 :> (#·.succ.succ))))
      (ψ.piInv.rew (Rew.subst (#1 :> (#·.succ.succ))))).unpair.pi

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

lemma models_exsPair (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f φ.exsPair.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [exsPair, models_sigma, exists_iff_exists_pair, exists_comm]
  simp [models_unpair]

lemma models_allPair (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1)) (e : Fin n → V) :
    Semiformula.Eval e f φ.allPair.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [allPair, models_pi, forall_iff_forall_pair, forall_comm]
  simp [models_unpair]

lemma models_andPair (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (φ.andPair ψ).val ↔
      Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val := by
  induction s generalizing Γ n with
  | zero => simp [andPair, val]
  | succ s ih =>
    rcases Γ
    · rw [andPair, models_sigma, exists_iff_exists_pair]
      simp [ih, models_unpair, models_sigmaInv, -val_sigmaInv, -val_piInv, Matrix.comp_vecCons,
        Function.comp_def, exists_and_left, exists_and_right]
    · simp [andPair, ih, models_piInv, -val_sigmaInv, -val_piInv, forall_and]

lemma models_orPair (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (φ.orPair ψ).val ↔
      Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val := by
  induction s generalizing Γ n with
  | zero => simp [orPair, val]
  | succ s ih =>
    rcases Γ
    · simp [orPair, ih, models_sigmaInv, -val_sigmaInv, -val_piInv, exists_or]
    · rw [orPair, models_pi, forall_iff_forall_pair]
      simp [ih, models_unpair, models_piInv, -val_sigmaInv, -val_piInv, Matrix.comp_vecCons,
        Function.comp_def, forall_or_left, forall_or_right]

end models

end FFL.FirstOrder.Bounding.Prenex
