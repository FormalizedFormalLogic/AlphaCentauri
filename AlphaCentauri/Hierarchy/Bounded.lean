module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy

/-! # $\Delta_0$ formulas

Foundation names the class $\Delta_0$ of formulas all of whose quantifiers are bounded
`Arithmetic.DeltaZero`; `Arithmetic.Hierarchy.zero_iff_delta_zero` identifies it with
`Hierarchy Γ 0`. `bounded_induction` is a recursor for `DeltaZero` that Foundation does not
provide.

`StrictHierarchy.of_bounded` places such a formula at the bottom of the strict hierarchy.
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language} [L.LT] {ξ : Type*} {n : ℕ} {φ ψ : Semiformula L ξ n}

open Arithmetic

-- `witnesses_verum`/`witnesses_identity` build a `DeltaZero` witness directly from its shape;
-- these are intro rules for goals like `DeltaZero (.rel r v)`.
attribute [grind .] Semiformula.Bounded.verum Semiformula.Bounded.falsum Semiformula.Bounded.rel
  Semiformula.Bounded.nrel

/-- A `DeltaZero` formula sits at every zero level of the arithmetical hierarchy. -/
@[grind ←]
theorem Semiformula.Bounded.hierarchy {Γ : Polarity} (h : DeltaZero φ) : Hierarchy Γ 0 φ :=
  Hierarchy.zero_iff_delta_zero.mpr h

/-- A `DeltaZero` formula is strictly `Γ`-[s] at every level. -/
@[grind =>]
theorem Arithmetic.StrictHierarchy.of_bounded {Γ : Polarity} {s : ℕ} (h : DeltaZero φ) :
    StrictHierarchy Γ s φ := .of_deltaZero h.hierarchy

namespace Semiformula.Bounded

@[simp] lemma imp_iff : DeltaZero (φ 🡒 ψ) ↔ DeltaZero φ ∧ DeltaZero ψ := by
  simp [← Hierarchy.zero_iff_delta_zero (Γ := 𝚺), Hierarchy.pi_zero_iff_sigma_zero]

@[simp] lemma ballLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    DeltaZero (φ.ballLT t) ↔ DeltaZero φ := by
  simp [← Hierarchy.zero_iff_delta_zero (Γ := 𝚺)]

@[simp] lemma bexsLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    DeltaZero (φ.bexsLT t) ↔ DeltaZero φ := by
  simp [← Hierarchy.zero_iff_delta_zero (Γ := 𝚺)]

lemma of_open (h : φ.Open) : DeltaZero φ := by
  simpa [← Hierarchy.zero_iff_delta_zero (Γ := 𝚺)] using Hierarchy.of_open (Γ := 𝚺) (s := 0) h

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
    (hAnd : ∀ n φ ψ, DeltaZero φ → DeltaZero ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, DeltaZero φ → DeltaZero ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, DeltaZero φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, DeltaZero φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : DeltaZero φ → P n φ
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
    (hAnd : ∀ n φ ψ, DeltaZero φ → DeltaZero ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, DeltaZero φ → DeltaZero ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, DeltaZero φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, DeltaZero φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : DeltaZero φ → P n φ :=
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
