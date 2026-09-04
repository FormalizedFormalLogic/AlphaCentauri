module

public import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Two gaps in Foundation's `Semiformula` API

Foundation proves `Semiformula.complexity_rew`, that a rewriting leaves the complexity of a
formula alone, but states no counterpart for the quantifier rank `Semiformula.qr`. Substituting
terms touches neither the quantifier prefix nor the propositional skeleton, so `qr` is invariant
for the same reason.

It also stops halfway through the distinctness facts a subformula is proved to differ from its
compound by: `Semiformula.ne_or_left`, `Semiformula.ne_or_right` and `Semiformula.ex_ne_subst`
are there, their `⋏` and `∀¹` counterparts are not.

Finally, the logical notations `⊤`, `⊥`, `⋏`, `⋎`, `∀¹`, `∃¹` reach `Semiformula`'s constructors
through type classes, so `grind` does not see two formulas with different outermost connectives as
two different constructor applications, and cannot discharge the head-distinctness side conditions
that a syntactic induction over a sequent calculus produces at every step. Six `@[grind =]`
equations restore that. All of this belongs in Foundation.
-/

@[expose] public section

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂ : ℕ}

/-- A rewriting preserves the quantifier rank, exactly as it preserves the complexity
(`Semiformula.complexity_rew`). -/
@[simp] lemma qr_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : (ω ▹ φ).qr = φ.qr := by
  induction φ using Semiformula.rec' generalizing n₂ <;> simp [*]

/-- Substituting a term for the sole free variable of a `Semiformula _ _ 1` preserves the
quantifier rank. -/
@[simp] lemma qr_substs (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) : (φ/[t]).qr = φ.qr :=
  qr_rew _ φ

/-- The `⋏` counterpart of `Semiformula.ne_or_left`. -/
@[simp, grind .] lemma ne_and_left (φ ψ : Semiformula L ξ n) : φ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

/-- The `⋏` counterpart of `Semiformula.ne_or_right`. -/
@[simp, grind .] lemma ne_and_right (φ ψ : Semiformula L ξ n) : ψ ≠ φ ⋏ ψ :=
  ne_of_ne_complexity (by simp)

/-- The `∀¹` counterpart of `Semiformula.ex_ne_subst`. -/
@[simp, grind .] lemma all_ne_subst (φ : Semiformula L ξ 1) (t : Semiterm L ξ 0) : φ/[t] ≠ ∀¹ φ :=
  ne_of_ne_complexity (by simp)

attribute [grind .] ne_or_left ne_or_right ex_ne_subst

section GrindConstructors

/-! ### Reducing the logical notations to constructors

`grind` decides disequality of constructor applications, but `φ ⋎ ψ` is a `Vee.vee` application
until the instance is unfolded. These `rfl` equations let it normalize, so that
`Semiformula.rel r v ≠ φ ⋎ ψ` and its two dozen siblings need no lemma of their own. -/

@[grind =] lemma verum_eq : (⊤ : Semiformula L ξ n) = Semiformula.verum := rfl

@[grind =] lemma falsum_eq : (⊥ : Semiformula L ξ n) = Semiformula.falsum := rfl

@[grind =] lemma and_eq (φ ψ : Semiformula L ξ n) : φ ⋏ ψ = Semiformula.and φ ψ := rfl

@[grind =] lemma or_eq (φ ψ : Semiformula L ξ n) : φ ⋎ ψ = Semiformula.or φ ψ := rfl

@[grind =] lemma all_eq (φ : Semiformula L ξ (n + 1)) : ∀¹ φ = Semiformula.all φ := rfl

@[grind =] lemma exs_eq (φ : Semiformula L ξ (n + 1)) : ∃¹ φ = Semiformula.exs φ := rfl

end GrindConstructors

end LO.FirstOrder.Semiformula
