module

public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# Connectives on prenex formulas over $\mathsf{IOpen}$

Prenex formulas of a given polarity and level with a bounded matrix are closed, up to
equivalence in every model of $\mathsf{IOpen}$, under conjunction, disjunction, and an outer
quantifier of the leading polarity. Consequently every theory containing $\mathsf{IOpen}$
proves each such combination of prenex formulas equivalent to a prenex formula of the same
polarity and level. Every level also contains a sentence provable and one refutable in every
theory containing equality.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] {P : V → Prop}

lemma exists_iff_exists_pair : (∃ z, P z) ↔ ∃ x y, P ⟪x, y⟫ :=
  ⟨fun ⟨z, h⟩ ↦ ⟨π₁ z, π₂ z, by simpa using h⟩, fun ⟨x, y, h⟩ ↦ ⟨⟪x, y⟫, h⟩⟩

lemma forall_iff_forall_pair : (∀ z, P z) ↔ ∀ x y, P ⟪x, y⟫ :=
  ⟨fun h x y ↦ h ⟪x, y⟫, fun h z ↦ by simpa using h (π₁ z) (π₂ z)⟩

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Bounding

namespace Prenex

open Arithmetic

variable {Γ : Polarity} {s : ℕ} {ξ : Type*} {n : ℕ}

/-- The formula whose value at `z, e` is the value of `φ` at `π₁ z, π₂ z, e`. -/
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

/-- A formula of the same polarity and level as `φ`, equivalent to `∃¹ φ` in every model of
`𝗜𝗢𝗽𝗲𝗻`. -/
def exsPair (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n :=
  φ.sigmaInv.unpair.sigma

/-- A formula of the same polarity and level as `φ`, equivalent to `∀¹ φ` in every model of
`𝗜𝗢𝗽𝗲𝗻`. -/
def allPair (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ n :=
  φ.piInv.unpair.pi

/-- A formula equivalent to `φ ⋏ ψ` in every model of `𝗜𝗢𝗽𝗲𝗻`. -/
def andPair : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => ⟨⟨_, .and φ.matrix.bounded ψ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, φ, ψ =>
    (andPair (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))
      (ψ.sigmaInv.rew (Rew.subst (#1 :> (#·.succ.succ))))).unpair.sigma
  | 𝚷, _ + 1, _, φ, ψ => (andPair φ.piInv ψ.piInv).pi

/-- A formula equivalent to `φ ⋎ ψ` in every model of `𝗜𝗢𝗽𝗲𝗻`. -/
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
      simp [ih, models_unpair, Matrix.comp_vecCons, Function.comp_def, exists_and_left,
        exists_and_right]
    · simp [andPair, ih, models_piInv, -val_piInv, forall_and]

lemma models_orPair (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (e : Fin n → V) :
    Semiformula.Eval e f (φ.orPair ψ).val ↔
      Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val := by
  induction s generalizing Γ n with
  | zero => simp [orPair, val]
  | succ s ih =>
    rcases Γ
    · simp [orPair, ih, models_sigmaInv, -val_sigmaInv, exists_or]
    · rw [orPair, models_pi, forall_iff_forall_pair]
      simp [ih, models_unpair, Matrix.comp_vecCons, Function.comp_def, forall_or_left,
        forall_or_right]

end models

end Prenex

namespace PrenexHierarchy

open Arithmetic

variable (T : ArithmeticTheory) {Γ : Polarity} {s n : ℕ}

section

variable [𝗘𝗤 ℒₒᵣ ⪯ T]

theorem exists_provable : ∃ σ : ArithmeticSentence, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s σ ∧ T ⊢ σ := by
  use (Prenex.verum : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0).val
  and_intros
  · exact Prenex.val_prenexHierarchy
  · apply Arithmetic.complete.{0} T
    intro V _ _
    simp [models_iff, Prenex.models_verum]

theorem exists_refutable :
    ∃ σ : ArithmeticSentence, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s σ ∧ T ⊢ ∼σ := by
  use (Prenex.falsum : ℬ[<, ℒₒᵣ].Prenex Γ s Empty 0).val
  and_intros
  · exact Prenex.val_prenexHierarchy
  · apply Arithmetic.complete.{0} T
    intro V _ _
    simp [models_iff, Prenex.models_falsum]

end

variable [𝗜𝗢𝗽𝗲𝗻 ⪯ T]

private lemma provable_iff_of_models_iff {φ ψ : ArithmeticSemisentence n}
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (e : Fin n → V),
      V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗢𝗽𝗲𝗻) inferInstance
  apply Arithmetic.provable_iff_of_models_iff.{0}
  intro V _ _ e
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T)
  exact h V e

variable {σ τ : ArithmeticSemisentence n}

theorem exists_provable_iff_and (hσ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s σ)
    (hτ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s τ) :
    ∃ ρ, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s ρ ∧ T ⊢ ∀¹* (ρ 🡘 σ ⋏ τ) := by
  obtain ⟨σ, rfl⟩ := hσ
  obtain ⟨τ, rfl⟩ := hτ
  use (σ.andPair τ).val
  and_intros
  · exact Prenex.val_prenexHierarchy
  · apply provable_iff_of_models_iff
    intro V _ _ e
    simp [Prenex.models_andPair]

theorem exists_provable_iff_or (hσ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s σ)
    (hτ : ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s τ) :
    ∃ ρ, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s ρ ∧ T ⊢ ∀¹* (ρ 🡘 σ ⋎ τ) := by
  obtain ⟨σ, rfl⟩ := hσ
  obtain ⟨τ, rfl⟩ := hτ
  use (σ.orPair τ).val
  and_intros
  · exact Prenex.val_prenexHierarchy
  · apply provable_iff_of_models_iff
    intro V _ _ e
    simp [Prenex.models_orPair]

theorem exists_provable_iff_exs {σ : ArithmeticSemisentence (n + 1)}
    (h : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 (s + 1) σ) :
    ∃ ρ, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 (s + 1) ρ ∧ T ⊢ ∀¹* (ρ 🡘 ∃¹ σ) := by
  obtain ⟨σ, rfl⟩ := h
  use σ.exsPair.val
  and_intros
  · exact Prenex.val_prenexHierarchy
  · apply provable_iff_of_models_iff
    intro V _ _ e
    simp [Prenex.models_exsPair, -Prenex.val_sigmaInv]

theorem exists_provable_iff_all {σ : ArithmeticSemisentence (n + 1)}
    (h : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (s + 1) σ) :
    ∃ ρ, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (s + 1) ρ ∧ T ⊢ ∀¹* (ρ 🡘 ∀¹ σ) := by
  obtain ⟨σ, rfl⟩ := h
  use σ.allPair.val
  and_intros
  · exact Prenex.val_prenexHierarchy
  · apply provable_iff_of_models_iff
    intro V _ _ e
    simp [Prenex.models_allPair, -Prenex.val_piInv]

end PrenexHierarchy

end FFL.FirstOrder.Bounding
