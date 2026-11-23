module

public import AlphaCentauri.ToFoundation.FirstOrder.Syntax
public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.Schemata.BoundedInduction

/-!
# Statements of Fermat's Last Theorem and its cases

`fermatLastTheorem n` is Fermat's Last Theorem for exponent `n`. This file also defines Case I and
Case II of it and Bézout's theorem.

- [Smi92b]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- Fermat's Last Theorem for exponent `n`. -/
def fermatLastTheorem (n : ℕ) : ArithmeticSentence :=
  “∀ x y z, x ^' n + y ^' n = z ^' n → x = 0 ∨ y = 0 ∨ z = 0”

/-- Bézout's theorem: any `x` and nonzero `y` have a common divisor `z` with `s y = t x + z`.
Smith prints it without the hypothesis `y ≠ 0`, which `x = 1`, `y = 0` violates.
- [Smi92b, Definition 3.5] -/
def bezout : ArithmeticSentence := “∀ x y, y ≠ 0 → ∃ z s t, s * y = t * x + z ∧ z ∣ x ∧ z ∣ y”

/-- Case I of Fermat's Last Theorem for exponent `n`: every solution of `xⁿ + yⁿ = zⁿ` has
`n ∣ x y z`.
- [Smi92b, §2] -/
def fermatLastTheoremCaseOne (n : ℕ) : ArithmeticSentence :=
  “∀ x y z, x ^' n + y ^' n = z ^' n → ↑n ∣ x * y * z”

/-- Case II of Fermat's Last Theorem for exponent `n`: every solution of `xⁿ + yⁿ = zⁿ` with
`n ∣ x y z` is trivial.
- [Smi92b, §2] -/
def fermatLastTheoremCaseTwo (n : ℕ) : ArithmeticSentence :=
  “∀ x y z, x ^' n + y ^' n = z ^' n → ↑n ∣ x * y * z → x = 0 ∨ y = 0 ∨ z = 0”

/-- `xⁿ ± yⁿ = z²` has only trivial solutions.
- [Smi92b, Question 5.6] -/
def powerAddPowerNeSquare (n : ℕ) : ArithmeticSentence :=
  “∀ x y z, x ^' n + y ^' n = z * z ∨ x ^' n = y ^' n + z * z →
    x = 0 ∨ y = 0 ∨ z = 0”

end FFL.FirstOrder.Arithmetic
