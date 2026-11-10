module

public import AlphaCentauri.Model.OpenInduction
public import AlphaCentauri.ToFoundation.FirstOrder.Semiformula
public import AlphaCentauri.Schemata.DeltaInduction

/-!
# Statements of Fermat's Last Theorem and its cases

`fermatLastTheorem n` is Fermat's Last Theorem for exponent `n`. This file also defines Case I and
Case II of it and Bézout's theorem, and states the open problems about them as propositions.

- [Smi92b]
- [Smi93]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open OpenPredicate

/-- Fermat's Last Theorem for exponent `n`. -/
def fermatLastTheorem (n : ℕ) : ArithmeticSentence :=
  “∀ x y z, x ^' n + y ^' n = z ^' n → x = 0 ∨ y = 0 ∨ z = 0”

/-- $\mathsf{I}\mathsf{E}_2$ proves Fermat's Last Theorem for every odd exponent $n \ge 5$. An
open problem.
- [Smi93, Question 5.6] -/
def ProvableFermatLastTheoremIE2 : Prop := ∀ n : ℕ, Odd n → 5 ≤ n → 𝗜𝗘₂ ⊢ fermatLastTheorem n

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

/-- $\mathsf{IOpen} + \mathrm{Bez}$ proves Case II of Fermat's Last Theorem for some exponent
$n \ge 3$. An open problem.
- [Smi92b, Question 5.3] -/
def ExistsProvableFermatLastTheoremCaseTwoIOpenBezout : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ insert bezout 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseTwo n

/-- $\mathsf{IE}_1$ proves Case I of Fermat's Last Theorem for each standard $n \ge 3$. An open
problem; since $\mathsf{IE}_1$ proves $\mathsf{IOpen} + \mathrm{Bez}$, which proves
$\mathsf{IOpen} + \mathrm{GCD}$, it is equivalent to asking whether Case I is provable in any of
the three.
- [Smi92b, Question 5.5]
- [Smi92b, Lemma 3.11] -/
def ProvableFermatLastTheoremCaseOneIE1 : Prop :=
  ∀ n : ℕ, 3 ≤ n → 𝗜𝗘₁ ⊢ fermatLastTheoremCaseOne n

/-- $\mathsf{IE}_1$ proves Fermat's Last Theorem for each even standard $n > 2$. An open problem.
- [Smi92b, Question 5.6] -/
def ProvableFermatLastTheoremIE1OfEven : Prop :=
  ∀ n : ℕ, Even n → 2 < n → 𝗜𝗘₁ ⊢ fermatLastTheorem n

/-- $\mathsf{IE}_1$ proves that $x^n \pm y^n = z^2$ has no nontrivial solutions for each even
standard $n \ge 4$. An open problem.
- [Smi92b, Question 5.6] -/
def ProvablePowerAddPowerNeSquareIE1 : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → 𝗜𝗘₁ ⊢ powerAddPowerNeSquare n

end FFL.FirstOrder.Arithmetic
