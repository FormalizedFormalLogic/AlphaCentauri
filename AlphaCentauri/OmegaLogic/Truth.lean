module

public import Foundation.FirstOrder.Arithmetic.Basic

/-!
# Truth of arithmetic literals in `ℕ`

Truth of an arithmetic formula in the standard model `ℕ`, of its numeral instances, and of signed
atomic literals.

- [Tow20, Section 13]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.OmegaLogic

section Truth

variable {φ ψ : ArithmeticFormula ℕ} {φₓ : ArithmeticSemiformula ℕ 1}

/-- Truth of an arithmetic formula in the standard model `ℕ`.

- [Tow20, Section 13] -/
def LitTrue (φ : ArithmeticFormula ℕ) : Prop := Semiformula.Evalf (M := ℕ) id φ

@[simp, grind =] lemma litTrue_neg : LitTrue (∼φ) ↔ ¬LitTrue φ := by simp [LitTrue]

@[simp] lemma litTrue_verum : LitTrue ⊤ := by simp [LitTrue]

@[simp] lemma litTrue_falsum : ¬LitTrue ⊥ := by simp [LitTrue]

@[simp, grind =] lemma litTrue_and : LitTrue (φ ⋏ ψ) ↔ LitTrue φ ∧ LitTrue ψ := by simp [LitTrue]

@[simp, grind =] lemma litTrue_or : LitTrue (φ ⋎ ψ) ↔ LitTrue φ ∨ LitTrue ψ := by simp [LitTrue]

lemma litTrue_or_neg (φ : ArithmeticFormula ℕ) : LitTrue φ ∨ LitTrue (∼φ) := by simp [LitTrue, em]

/-- A universal formula is true exactly when all its numeral instances are true.

- [Tow20, Section 13] -/
@[simp, grind =]
lemma litTrue_all : LitTrue (∀¹ φₓ) ↔ ∀ n : ℕ, LitTrue (φₓ/[(↑n : ArithmeticTerm ℕ)]) := by
  simp [LitTrue]

/-- An existential formula is true exactly when some numeral instance is true.

- [Tow20, Section 13] -/
@[simp, grind =]
lemma litTrue_exs : LitTrue (∃¹ φₓ) ↔ ∃ n : ℕ, LitTrue (φₓ/[(↑n : ArithmeticTerm ℕ)]) := by
  simp [LitTrue]

/-- The atomic literal with positive polarity for `true` and negative polarity for `false`.

- [Tow20, Section 13] -/
def signedLit : Bool → {k : ℕ} → (ℒₒᵣ).Rel k → (Fin k → ArithmeticTerm ℕ) → ArithmeticFormula ℕ
  |  true, _, r, v => Semiformula.rel r v
  | false, _, r, v => Semiformula.nrel r v

variable {k : ℕ} {b : Bool} {r : (ℒₒᵣ).Rel k} {v : Fin k → ArithmeticTerm ℕ}

@[simp, grind =] lemma neg_signedLit : ∼(signedLit b r v) = signedLit (!b) r v := by
  cases b <;> simp [signedLit]

@[simp, grind .] lemma signedLit_ne_verum : signedLit b r v ≠ ⊤ := by cases b <;> simp [signedLit]

end Truth

end FFL.FirstOrder.Arithmetic.OmegaLogic
