module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy

/-! # $\Delta_0$ formulas

In Foundation the class $\Delta_0$ of formulas all of whose quantifiers are bounded by `<` is
`ℬ[<, L].Closure`; `Bounding.Hierarchy.zero_iff_bounded` identifies it with
`ℬ[<, L].Hierarchy Γ 0`. `bounded_induction` is a recursor for it on arithmetical formulas that
Foundation does not provide.

`StrictHierarchy.of_bounded` places such a formula at the bottom of the strict hierarchy.
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language} [L.LT] {ξ : Type*} {n : ℕ} {φ ψ : Semiformula L ξ n}

open Arithmetic

-- `witnesses_verum`/`witnesses_identity` build a bounded witness directly from its shape;
-- these are intro rules for goals like `ℬ[<, L].Closure (.rel r v)`.
attribute [grind .] Bounding.Closure.verum Bounding.Closure.falsum Bounding.Closure.rel
  Bounding.Closure.nrel

/-- A bounded formula sits at every zero level of the arithmetical hierarchy. -/
@[grind ←]
theorem Bounding.Closure.hierarchy {Γ : Polarity} (h : ℬ[<, L].Closure φ) :
    ℬ[<, L].Hierarchy Γ 0 φ :=
  .bounded _ _ _ h

/-- A bounded formula is strictly `Γ`-[s] at every level. -/
@[grind =>]
theorem Arithmetic.StrictHierarchy.of_bounded {Γ : Polarity} {s : ℕ} (h : ℬ[<, L].Closure φ) :
    StrictHierarchy Γ s φ := (zero h).mono (Nat.zero_le s)

namespace Bounding.Closure

lemma arithmetic_ball {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive)
    (h : ℬ[<, L].Closure φ) : ℬ[<, L].Closure (∀¹[“x. x < !!t”] φ) :=
  ball (R := Semiformula.Operator.LT.lt) (by rfl) ht h

lemma arithmetic_bexs {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive)
    (h : ℬ[<, L].Closure φ) : ℬ[<, L].Closure (∃¹[“x. x < !!t”] φ) :=
  bexs (R := Semiformula.Operator.LT.lt) (by rfl) ht h

@[simp] lemma imp_iff : ℬ[<, L].Closure (φ 🡒 ψ) ↔ ℬ[<, L].Closure φ ∧ ℬ[<, L].Closure ψ := by
  simp [Semiformula.imp_eq]

@[simp] lemma ballLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    ℬ[<, L].Closure (φ.ballLT t) ↔ ℬ[<, L].Closure φ := by
  simp [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]

@[simp] lemma bexsLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    ℬ[<, L].Closure (φ.bexsLT t) ↔ ℬ[<, L].Closure φ := by
  simp [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]

lemma of_open (h : φ.Open) : ℬ[<, L].Closure φ :=
  Bounding.Hierarchy.zero_iff_bounded.mp (Bounding.Hierarchy.of_open (Γ := 𝚺) (s := 0) h)

end Bounding.Closure

namespace Arithmetic

/-- Recursion on bounded arithmetical formulas. -/
lemma bounded_induction {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : ℬ[<, ℒₒᵣ].Closure φ → P n φ
  |                Bounding.Closure.verum _ => hVerum _
  |               Bounding.Closure.falsum _ => hFalsum _
  |  Bounding.Closure.rel Language.Eq.eq v => by
      simpa [←Matrix.fun_eq_vec_two] using hEQ _ (v 0) (v 1)
  | Bounding.Closure.nrel Language.Eq.eq v => by
      simpa [←Matrix.fun_eq_vec_two] using hNEQ _ (v 0) (v 1)
  |  Bounding.Closure.rel Language.LT.lt v => by
      simpa [←Matrix.fun_eq_vec_two] using hLT _ (v 0) (v 1)
  | Bounding.Closure.nrel Language.LT.lt v => by
      simpa [←Matrix.fun_eq_vec_two] using hNLT _ (v 0) (v 1)
  |                Bounding.Closure.and hp hq =>
    hAnd _ _ _ hp hq
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hq)
  |                 Bounding.Closure.or hp hq =>
    hOr _ _ _ hp hq
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hq)
  |               Bounding.Closure.ball hR pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa [Semiformula.Operator.lt_def] using hBall _ t _ hp
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
  |               Bounding.Closure.bexs hR pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa [Semiformula.Operator.lt_def] using hBex _ t _ hp
      (bounded_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)

/-- Recursion on bounded arithmetical formulas, with the literals collected into a single case for
open formulas. -/
lemma bounded_induction_open {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hOpen : ∀ n φ, Semiformula.Open φ → P n φ)
    (hAnd : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : ℬ[<, ℒₒᵣ].Closure φ → P n φ :=
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
