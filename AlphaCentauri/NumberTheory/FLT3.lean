module

public import AlphaCentauri.ToFoundation.LeastNumberPrinciple
public import AlphaCentauri.ToMathlib.FLT3.Descent

/-!
# Fermat's Last Theorem for exponent 3 in $\mathsf{I}\mathsf{E}_1$

$\mathsf{I}\mathsf{E}_1$ is induction for bounded existential formulas over $\mathsf{PA}^-$.
Over a model $V$ of $\mathsf{I}\mathsf{E}_1$, the ring of differences of $V$ satisfies the least
number principle `LeastNumberPrinciple` for bounded existential open predicates, and
`FermatThree.flt3_of_leastNumberPrinciple` applies to it. Smith proved the statement over
$\mathsf{I}\mathsf{E}_2$ and asked whether $\mathsf{I}\mathsf{E}_1$ suffices, and whether
$\mathsf{I}\mathsf{E}_2$ proves the other odd exponents, which is open.

- [Wil85]
- [Smi93, Question 5.5, Question 5.6]
- [Smi92b, Question 5.1, Question 5.3, Question 5.5, Question 5.6]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open RingOfDifferences OpenPredicate

/-- Fermat's Last Theorem for exponent `n`. -/
def fermatLastTheorem (n : ℕ) : ArithmeticSentence :=
  “∀ x y z, x ^' n + y ^' n = z ^' n → x = 0 ∨ y = 0 ∨ z = 0”

/-- $\mathsf{I}\mathsf{E}_1$ proves Fermat's Last Theorem for exponent $3$.
- [Wil85]
- [Smi93, Question 5.5] -/
theorem provable_fermatLastTheorem_three_IE1 : 𝗜𝗘₁ ⊢ fermatLastTheorem 3 := by
  apply complete
  intro V _ hV
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := Semantics.ModelsSet.of_subset hV Set.subset_union_left
  have := Semantics.ModelsSet.of_subset hV Set.subset_union_right
  have hL := leastNumberPrinciple_of_models_induction (V := V)
  suffices ∀ a b c : V, a ^ 3 + b ^ 3 = c ^ 3 → a = 0 ∨ b = 0 ∨ c = 0 by
    simpa [models_iff, fermatLastTheorem]
  intro a b c h
  have e : of a ^ 3 + of b ^ 3 = of c ^ 3 := by simpa [map_add (of : V →+* _)] using congrArg of h
  simpa [map_eq_zero_iff _ of_injective] using FermatThree.flt3_of_leastNumberPrinciple hL _ _ _ e

/-- $\mathsf{I}\mathsf{E}_2$ proves Fermat's Last Theorem for every odd exponent $n \ge 5$. An
open problem.
- [Smi93, Question 5.6] -/
axiom provable_fermatLastTheorem_IE2 {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n) :
    𝗜𝗘₂ ⊢ fermatLastTheorem n

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

/-- Some model of $\mathsf{IOpen}$ contains a counterexample to Case I of Fermat's Last Theorem
for some exponent $n \ge 3$. An open problem.
- [Smi92b, Question 5.1] -/
axiom exists_not_provable_fermatLastTheoremCaseOne_IOpen :
    ∃ n : ℕ, 3 ≤ n ∧ ¬𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseOne n

/-- $\mathsf{IOpen} + \mathrm{Bez}$ proves Case II of Fermat's Last Theorem for some exponent
$n \ge 3$. An open problem.
- [Smi92b, Question 5.3] -/
axiom exists_provable_fermatLastTheoremCaseTwo_IOpen_bezout :
    ∃ n : ℕ, 3 ≤ n ∧ insert bezout 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseTwo n

/-- $\mathsf{IE}_1$ proves Case I of Fermat's Last Theorem for each standard $n \ge 3$. An open
problem; since $\mathsf{IE}_1$ proves $\mathsf{IOpen} + \mathrm{Bez}$, which proves
$\mathsf{IOpen} + \mathrm{GCD}$, it is equivalent to asking whether Case I is provable in any of
the three.
- [Smi92b, Question 5.5]
- [Smi92b, Lemma 3.11] -/
axiom provable_fermatLastTheoremCaseOne_IE1 {n : ℕ} (hn : 3 ≤ n) :
    𝗜𝗘₁ ⊢ fermatLastTheoremCaseOne n

/-- $\mathsf{IE}_1$ proves Fermat's Last Theorem for each even standard $n > 2$. An open problem.
- [Smi92b, Question 5.6] -/
axiom provable_fermatLastTheorem_IE1_of_even {n : ℕ} (hn : Even n) (h : 2 < n) :
    𝗜𝗘₁ ⊢ fermatLastTheorem n

/-- $\mathsf{IE}_1$ proves that $x^n \pm y^n = z^2$ has no nontrivial solutions for each even
standard $n \ge 4$. An open problem.
- [Smi92b, Question 5.6] -/
axiom provable_powerAddPowerNeSquare_IE1 {n : ℕ} (hn : Even n) (h : 4 ≤ n) :
    𝗜𝗘₁ ⊢ powerAddPowerNeSquare n

end FFL.FirstOrder.Arithmetic
