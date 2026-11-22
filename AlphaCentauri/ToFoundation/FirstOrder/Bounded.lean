module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-! # $\Delta_0$ formulas

In Foundation the class $\Delta_0$ of formulas all of whose quantifiers are bounded by `<` is
`ℬ[<, L].Closure`; `Bounding.Hierarchy.zero_iff_bounded` identifies it with
`ℬ[<, L].Hierarchy Γ 0`. `bounded_induction` is a recursor for it on arithmetical formulas that
Foundation does not provide.
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

namespace Bounding.Closure

lemma arithmetic_ball {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive)
    (h : ℬ[<, L].Closure φ) : ℬ[<, L].Closure (∀¹[“x. x < !!t”] φ) :=
  ball (R := Semiformula.Operator.LT.lt) (by rfl) ht h

lemma arithmetic_bexs {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive)
    (h : ℬ[<, L].Closure φ) : ℬ[<, L].Closure (∃¹[“x. x < !!t”] φ) :=
  bexs (R := Semiformula.Operator.LT.lt) (by rfl) ht h

@[simp]
lemma imp_iff : ℬ[<, L].Closure (φ 🡒 ψ) ↔ ℬ[<, L].Closure φ ∧ ℬ[<, L].Closure ψ := by
  simp [Semiformula.imp_eq]

@[simp]
lemma ballLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    ℬ[<, L].Closure (φ.ballLT t) ↔ ℬ[<, L].Closure φ := by
  simp [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]

@[simp]
lemma bexsLT_iff {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    ℬ[<, L].Closure (φ.bexsLT t) ↔ ℬ[<, L].Closure φ := by
  simp [← Bounding.Hierarchy.zero_iff_bounded (Γ := 𝚺)]

lemma of_open (h : φ.Open) : ℬ[<, L].Closure φ :=
  Bounding.Hierarchy.zero_iff_bounded.mp (Bounding.Hierarchy.of_open (Γ := 𝚺) (s := 0) h)

end Bounding.Closure

namespace Bounding.Closure

/-- Recursion on `ℬ[<, L]`-bounded formulas, with the literals collected into a single case for open
formulas. -/
lemma induction_open {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hOpen : ∀ n φ, Semiformula.Open φ → P n φ)
    (hAnd : ∀ n φ ψ, ℬ[<, L].Closure φ → ℬ[<, L].Closure ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ[<, L].Closure φ → ℬ[<, L].Closure ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, L].Closure φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, ℬ[<, L].Closure φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (h : ℬ[<, L].Closure φ) : P n φ := by
  induction h with
  | verum | falsum | rel | nrel => exact hOpen _ _ (by simp)
  | and hp hq ihp ihq => exact hAnd _ _ _ hp hq ihp ihq
  | or hp hq ihp ihq => exact hOr _ _ _ hp hq ihp ihq
  | ball hR pt hp ih =>
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp pt
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa [Semiformula.Operator.lt_def] using hBall _ t _ hp ih
  | bexs hR pt hp ih =>
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp pt
    obtain rfl := Set.mem_singleton_iff.mp hR
    simpa [Semiformula.Operator.lt_def] using hBex _ t _ hp ih

end Bounding.Closure

end FFL.FirstOrder
