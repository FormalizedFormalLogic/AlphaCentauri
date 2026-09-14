module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-!
# Axiomatizability by a class of the arithmetical hierarchy

`FFL.FirstOrder.Arithmetic.Axiomatizable Γ n T` says that `T` is $\Gamma_n$-axiomatizable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- `T` is $\Gamma_n$-axiomatizable: some theory all of whose members are $\Gamma_n$ sentences
proves exactly the theorems of `T`. The axioms of `T` itself need not be $\Gamma_n$.
- [HP98, Discussion III.2.28] -/
def Axiomatizable (Γ : Polarity) (n : ℕ) (T : ArithmeticTheory) : Prop :=
  ∃ U : ArithmeticTheory, (∀ σ ∈ U, Hierarchy Γ n σ) ∧ U ≊ T

end FFL.FirstOrder.Arithmetic
