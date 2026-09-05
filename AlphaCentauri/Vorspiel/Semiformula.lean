module

public import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Two gaps in Foundation's `Semiformula` API

Quantifier-rank invariance, distinctness lemmas, and constructor equations for `Semiformula`.
-/

@[expose] public section

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}

/-- A rewriting preserves quantifier rank. -/
@[simp] lemma qr_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : (ω ▹ φ).qr = φ.qr := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- Substituting a term for the sole free variable of a `Semiformula _ _ 1` preserves the
quantifier rank. -/
@[simp] lemma qr_substs (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) : (φ/[t]).qr = φ.qr :=
  qr_rew _ φ

/-- A formula differs from its conjunction with another formula. -/
@[simp, grind .] lemma ne_and_left (φ ψ : Semiformula L ξ n) : φ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

/-- A formula differs from a conjunction having it as the right conjunct. -/
@[simp, grind .] lemma ne_and_right (φ ψ : Semiformula L ξ n) : ψ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

/-- Substitution into a formula differs from its universal closure. -/
@[simp, grind .] lemma all_ne_subst (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) : φ/[t] ≠ ∀¹ φ :=
  ne_of_ne_complexity (by simp)

attribute [grind .] ne_or_left ne_or_right ex_ne_subst

section GrindConstructors

/-! ### Reducing the logical notations to constructors

Equations identifying logical notation with `Semiformula` constructors. -/

@[grind =] lemma verum_eq : (⊤ : Semiformula L ξ n) = Semiformula.verum := rfl

@[grind =] lemma falsum_eq : (⊥ : Semiformula L ξ n) = Semiformula.falsum := rfl

@[grind =] lemma and_eq (φ ψ : Semiformula L ξ n) : φ ⋏ ψ = Semiformula.and φ ψ := rfl

@[grind =] lemma or_eq (φ ψ : Semiformula L ξ n) : φ ⋎ ψ = Semiformula.or φ ψ := rfl

@[grind =] lemma all_eq (φ : Semiformula L ξ (n + 1)) : ∀¹ φ = Semiformula.all φ := rfl

@[grind =] lemma exs_eq (φ : Semiformula L ξ (n + 1)) : ∃¹ φ = Semiformula.exs φ := rfl

end GrindConstructors

end LO.FirstOrder.Semiformula
