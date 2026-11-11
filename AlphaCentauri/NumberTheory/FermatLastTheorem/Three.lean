module

public import AlphaCentauri.NumberTheory.FermatLastTheorem.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.LeastNumberPrinciple
public import AlphaCentauri.ToMathlib.NumberTheory.FLT.Three

/-!
# Fermat's Last Theorem for exponent three in $\mathsf{I}\mathsf{E}_1$

$\mathsf{I}\mathsf{E}_1$ is induction for bounded existential formulas over $\mathsf{PA}^-$. This
file proves that $\mathsf{I}\mathsf{E}_1$ proves Fermat's Last Theorem for exponent $3$.

- [Wil85]
- [Smi93]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open RingOfDifferences OpenPredicate

/-- $\mathsf{I}\mathsf{E}_1$ proves Fermat's Last Theorem for exponent $3$.
- [Wil85]
- [Smi93, Question 5.5] -/
theorem provable_fermatLastTheorem_three_IE1 : 𝗜𝗘₁ ⊢ fermatLastTheorem 3 := by
  apply complete
  intro V _ hV
  have hL := leastNumberPrinciple_of_models_induction (V := V)
  suffices ∀ a b c : V, a ^ 3 + b ^ 3 = c ^ 3 → a = 0 ∨ b = 0 ∨ c = 0 by
    simpa [models_iff, fermatLastTheorem]
  intro a b c h
  have e : of a ^ 3 + of b ^ 3 = of c ^ 3 := by simpa [map_add (of : V →+* _)] using congrArg of h
  simpa [map_eq_zero_iff _ of_injective] using FermatThree.flt3_of_leastNumberPrinciple hL _ _ _ e

end FFL.FirstOrder.Arithmetic
