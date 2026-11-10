module

public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The MRDP theorem over $\mathsf{I}\Delta_0$

Whether every $\Delta_0$ formula is equivalent over $\mathsf{I}\Delta_0$, or over
$\mathsf{I}\Delta_0 + \Omega_1$, to a Diophantine formula is an open problem. A positive answer
would give $\mathsf{NP} = \mathsf{coNP}$, as Wilkie observed.

- [DAq05, Question 8.1]
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A Diophantine formula: a block of existential quantifiers over an open formula.
- [DAq05, Question 8.1] -/
inductive Semiformula.Diophantine {L : Language} {ξ : Type*} :
    {n : ℕ} → Semiformula L ξ n → Prop
  | of_open {n : ℕ} {φ : Semiformula L ξ n} : φ.Open → Diophantine φ
  | exs {n : ℕ} {φ : Semiformula L ξ (n + 1)} : Diophantine φ → Diophantine (∃¹ φ)

namespace Arithmetic

/-- $\mathsf{I}\Delta_0$ proves that every $\Delta_0$ formula is equivalent to a Diophantine
formula. An open problem.
- [DAq05, Question 8.1] -/
def ExistsDiophantineEquivISigma0 : Prop :=
  ∀ φ : ArithmeticFormula ℕ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ →
    ∃ ψ : ArithmeticFormula ℕ, Semiformula.Diophantine ψ ∧ 𝗜𝚺₀ ⊢ (φ 🡘 ψ).univCl

/-- $\mathsf{I}\Delta_0 + \Omega_1$ proves that every $\Delta_0$ formula is equivalent to a
Diophantine formula. An open problem.
- [DAq05, §8] -/
def ExistsDiophantineEquivISigma0UnionOmega1 : Prop :=
  ∀ φ : ArithmeticFormula ℕ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ →
    ∃ ψ : ArithmeticFormula ℕ, Semiformula.Diophantine ψ ∧ 𝗜𝚺₀ ∪ 𝝮₁ ⊢ (φ 🡘 ψ).univCl

end Arithmetic

end FFL.FirstOrder
