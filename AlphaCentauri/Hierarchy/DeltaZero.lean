module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-! # Recursion on the bounded formulas

A recursor for bounded arithmetical formulas.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {ξ : Type*}

/-- Recursion on bounded arithmetical formulas. -/
lemma delta₀_induction {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 0 φ → Hierarchy 𝚺 0 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 0 φ → Hierarchy 𝚺 0 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 0 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, Hierarchy 𝚺 0 φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : Hierarchy 𝚺 0 φ → P n φ
  |               Hierarchy.verum _ _ _ => hVerum _
  |              Hierarchy.falsum _ _ _ => hFalsum _
  |  Hierarchy.rel _ _ Language.Eq.eq v => by simpa [←Matrix.fun_eq_vec_two] using hEQ _ (v 0) (v 1)
  | Hierarchy.nrel _ _ Language.Eq.eq v => by simpa [←Matrix.fun_eq_vec_two] using hNEQ _ (v 0) (v 1)
  |  Hierarchy.rel _ _ Language.LT.lt v => by simpa [←Matrix.fun_eq_vec_two] using hLT _ (v 0) (v 1)
  | Hierarchy.nrel _ _ Language.LT.lt v => by simpa [←Matrix.fun_eq_vec_two] using hNLT _ (v 0) (v 1)
  |                 Hierarchy.and hp hq =>
    hAnd _ _ _ hp hq
      (delta₀_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
      (delta₀_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hq)
  |                  Hierarchy.or hp hq =>
    hOr _ _ _ hp hq
      (delta₀_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
      (delta₀_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hq)
  |                Hierarchy.ball pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBall _ t _ hp
      (delta₀_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)
  |                Hierarchy.bexs pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBex _ t _ hp
      (delta₀_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hBex _ _ hp)

/-- Recursion on bounded arithmetical formulas, with the literals collected into a single case for
open formulas. -/
lemma delta₀_induction_open {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hOpen : ∀ n φ, Semiformula.Open φ → P n φ)
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 0 φ → Hierarchy 𝚺 0 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 0 φ → Hierarchy 𝚺 0 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 0 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, Hierarchy 𝚺 0 φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : Hierarchy 𝚺 0 φ → P n φ :=
  delta₀_induction
    (fun _ ↦ hOpen _ _ (by simp))
    (fun _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    hAnd hOr hBall hBex n φ

end FFL.FirstOrder.Arithmetic
