module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-! # Bounded formulas

`φ.Bounded` names the class $\Delta_0$ of formulas all of whose quantifiers are bounded. It is an
inductive definition in its own right, not a level of the arithmetical hierarchy;
`Semiformula.bounded_iff_hierarchy` identifies it with `Hierarchy Γ 0`, and `bounded_induction` is
the corresponding recursor.

This file is a local stand-in for the upstream definition proposed in
<https://github.com/FormalizedFormalLogic/Foundation/pull/838>. Once Foundation carries
`Semiformula.Bounded` itself, delete this file and import Foundation's in its place: everything
below is stated in the names the upstream definition will provide.
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language} [L.LT] {ξ : Type*}

open Arithmetic

/-- A bounded formula: one all of whose quantifiers are bounded, i.e. a $\Delta_0$ formula.
- [HP98, 0.30] -/
inductive Semiformula.Bounded : {n : ℕ} → Semiformula L ξ n → Prop
  | verum (n) : Bounded (⊤ : Semiformula L ξ n)
  | falsum (n) : Bounded (⊥ : Semiformula L ξ n)
  | rel {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Bounded (Semiformula.rel r v)
  | nrel {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Bounded (Semiformula.nrel r v)
  | and {n} {φ ψ : Semiformula L ξ n} : Bounded φ → Bounded ψ → Bounded (φ ⋏ ψ)
  | or {n} {φ ψ : Semiformula L ξ n} : Bounded φ → Bounded ψ → Bounded (φ ⋎ ψ)
  | ball {n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Bounded φ → Bounded (∀¹[“x. x < !!t”] φ)
  | bexs {n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Bounded φ → Bounded (∃¹[“x. x < !!t”] φ)

attribute [simp] Semiformula.Bounded.verum Semiformula.Bounded.falsum Semiformula.Bounded.rel
  Semiformula.Bounded.nrel

-- `witnesses_verum`/`witnesses_identity` build a `Bounded` witness directly from its shape;
-- these are intro rules for goals like `Semiformula.Bounded (.rel r v)`.
attribute [grind .] Semiformula.Bounded.verum Semiformula.Bounded.falsum Semiformula.Bounded.rel
  Semiformula.Bounded.nrel

variable {n : ℕ} {φ ψ : Semiformula L ξ n}

/-- A bounded formula sits at every zero level of the arithmetical hierarchy. -/
@[grind ←]
theorem Semiformula.Bounded.hierarchy {Γ : Polarity} (h : φ.Bounded) : Hierarchy Γ 0 φ := by
  induction h with
  | verum _ => exact Hierarchy.verum _ _ _
  | falsum _ => exact Hierarchy.falsum _ _ _
  | rel r v => exact Hierarchy.rel _ _ r v
  | nrel r v => exact Hierarchy.nrel _ _ r v
  | and _ _ ihφ ihψ => exact Hierarchy.and ihφ ihψ
  | or _ _ ihφ ihψ => exact Hierarchy.or ihφ ihψ
  | ball ht _ ih => exact Hierarchy.ball ht ih
  | bexs ht _ ih => exact Hierarchy.bexs ht ih

set_option linter.flexible false in
/-- A formula at a zero level of the arithmetical hierarchy is bounded. -/
@[grind →]
theorem Arithmetic.Hierarchy.bounded {Γ : Polarity} : Hierarchy Γ 0 φ → φ.Bounded := by
  generalize hs : 0 = s
  intro h
  induction h <;> try simp at hs
  case verum => exact .verum _
  case falsum => exact .falsum _
  case rel r v => exact .rel r v
  case nrel r v => exact .nrel r v
  case and ihφ ihψ => exact .and (ihφ hs) (ihψ hs)
  case or ihφ ihψ => exact .or (ihφ hs) (ihψ hs)
  case ball ht _ ih => exact .ball ht (ih hs)
  case bexs ht _ ih => exact .bexs ht (ih hs)

theorem Semiformula.bounded_iff_hierarchy {Γ : Polarity} : φ.Bounded ↔ Hierarchy Γ 0 φ :=
  ⟨Semiformula.Bounded.hierarchy, Arithmetic.Hierarchy.bounded⟩

namespace Semiformula.Bounded

@[simp] lemma and_iff : (φ ⋏ ψ).Bounded ↔ φ.Bounded ∧ ψ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺)]

@[simp] lemma or_iff : (φ ⋎ ψ).Bounded ↔ φ.Bounded ∧ ψ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺)]

@[simp] lemma neg_iff : (∼φ).Bounded ↔ φ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺), Hierarchy.pi_zero_iff_sigma_zero]

@[simp] lemma imp_iff : (φ 🡒 ψ).Bounded ↔ φ.Bounded ∧ ψ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺), Hierarchy.pi_zero_iff_sigma_zero]

@[simp] lemma ball_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    (∀¹[“x. x < !!t”] φ).Bounded ↔ φ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺), ht]

@[simp] lemma bexs_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    (∃¹[“x. x < !!t”] φ).Bounded ↔ φ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺), ht]

@[simp] lemma ballLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    (φ.ballLT t).Bounded ↔ φ.Bounded := by simp [bounded_iff_hierarchy (Γ := 𝚺)]

@[simp] lemma bexsLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    (φ.bexsLT t).Bounded ↔ φ.Bounded := by simp [bounded_iff_hierarchy (Γ := 𝚺)]

@[simp] lemma rew_iff {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {φ : Semiformula L ξ₁ n₁} : (ω ▹ φ).Bounded ↔ φ.Bounded := by
  simp [bounded_iff_hierarchy (Γ := 𝚺)]

lemma rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁}
    (h : φ.Bounded) : (ω ▹ φ).Bounded := rew_iff.mpr h

lemma of_open (h : φ.Open) : φ.Bounded := by
  simpa [bounded_iff_hierarchy (Γ := 𝚺)] using Hierarchy.of_open (Γ := 𝚺) (s := 0) h

end Semiformula.Bounded

namespace Arithmetic

/-- Recursion on bounded arithmetical formulas. -/
lemma bounded_induction {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, φ.Bounded → ψ.Bounded → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, φ.Bounded → ψ.Bounded → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, φ.Bounded → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, φ.Bounded → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : φ.Bounded → P n φ
  |                Semiformula.Bounded.verum _ => hVerum _
  |               Semiformula.Bounded.falsum _ => hFalsum _
  |  Semiformula.Bounded.rel Language.Eq.eq v => by
      simpa [←Matrix.fun_eq_vec_two] using hEQ _ (v 0) (v 1)
  | Semiformula.Bounded.nrel Language.Eq.eq v => by
      simpa [←Matrix.fun_eq_vec_two] using hNEQ _ (v 0) (v 1)
  |  Semiformula.Bounded.rel Language.LT.lt v => by
      simpa [←Matrix.fun_eq_vec_two] using hLT _ (v 0) (v 1)
  | Semiformula.Bounded.nrel Language.LT.lt v => by
      simpa [←Matrix.fun_eq_vec_two] using hNLT _ (v 0) (v 1)
  |                Semiformula.Bounded.and hp hq =>
    hAnd _ _ _ hp hq
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hq)
  |                 Semiformula.Bounded.or hp hq =>
    hOr _ _ _ hp hq
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hq)
  |               Semiformula.Bounded.ball pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBall _ t _ hp
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
  |               Semiformula.Bounded.bexs pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBex _ t _ hp
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)

/-- Recursion on bounded arithmetical formulas, with the literals collected into a single case for
open formulas. -/
lemma bounded_induction_open {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hOpen : ∀ n φ, Semiformula.Open φ → P n φ)
    (hAnd : ∀ n φ ψ, φ.Bounded → ψ.Bounded → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, φ.Bounded → ψ.Bounded → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, φ.Bounded → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, φ.Bounded → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : φ.Bounded → P n φ :=
  bounded_induction
    (fun _ ↦ hOpen _ _ (by simp))
    (fun _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    hAnd hOr hBall hBex n φ

end Arithmetic

end FFL.FirstOrder
