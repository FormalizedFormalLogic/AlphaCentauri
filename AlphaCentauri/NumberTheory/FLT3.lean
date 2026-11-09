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

end FFL.FirstOrder.Arithmetic
