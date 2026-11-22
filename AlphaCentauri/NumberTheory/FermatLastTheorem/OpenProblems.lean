module

public import AlphaCentauri.NumberTheory.FermatLastTheorem.Basic
import AlphaCentauri.OpenProblem

/-!
# Open problems on Fermat's Last Theorem in weak arithmetic

The provability of Fermat's Last Theorem, its cases, and $x^n \pm y^n = z^2$ in
$\mathsf{IOpen} + \mathrm{Bez}$, $\mathsf{IE}_1$ and $\mathsf{IE}_2$, stated as propositions.

- [Smi92b]
- [Smi93]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open OpenPredicate

/-- Does $\mathsf{I}\mathsf{E}_2$ prove Fermat's Last Theorem for every odd exponent $n \ge 5$?
- [Smi93, Question 5.6] -/
open_problem provable_fermatLastTheorem_IE2_of_odd :=
  ∀ n : ℕ, Odd n → 5 ≤ n → 𝗜𝗘₂ ⊢ fermatLastTheorem n

/-- Does $\mathsf{IOpen} + \mathrm{Bez}$ prove Case II of Fermat's Last Theorem for some exponent
$n \ge 3$?
- [Smi92b, Question 5.3] -/
open_problem exists_provable_fermatLastTheoremCaseTwo_IOpen_bezout :=
  ∃ n : ℕ, 3 ≤ n ∧ insert bezout 𝗜𝗢𝗽𝗲𝗻 ⊢ fermatLastTheoremCaseTwo n

/-- Does $\mathsf{IE}_1$ prove Case I of Fermat's Last Theorem for each standard $n \ge 3$? Since
$\mathsf{IE}_1$ proves $\mathsf{IOpen} + \mathrm{Bez}$, which proves
$\mathsf{IOpen} + \mathrm{GCD}$, it is equivalent to asking whether Case I is provable in any of the
three.
- [Smi92b, Question 5.5, Lemma 3.11] -/
open_problem provable_fermatLastTheoremCaseOne_IE1 :=
  ∀ n : ℕ, 3 ≤ n → 𝗜𝗘₁ ⊢ fermatLastTheoremCaseOne n

/-- Does $\mathsf{IE}_1$ prove Fermat's Last Theorem for each even standard $n > 2$?
- [Smi92b, Question 5.6] -/
open_problem provable_fermatLastTheorem_IE1_of_even :=
  ∀ n : ℕ, Even n → 2 < n → 𝗜𝗘₁ ⊢ fermatLastTheorem n

/-- Does $\mathsf{IE}_1$ prove that $x^n \pm y^n = z^2$ has no nontrivial solutions for each even
standard $n \ge 4$?
- [Smi92b, Question 5.6] -/
open_problem provable_powerAddPowerNeSquare_IE1 :=
  ∀ n : ℕ, Even n → 4 ≤ n → 𝗜𝗘₁ ⊢ powerAddPowerNeSquare n

end FFL.FirstOrder.Arithmetic
