module

public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Open problems on $\mathsf{I}\Delta_0$ and $\Omega_1$

Whether adjoining $\Omega_1$ to $\mathsf{I}\Delta_0$ adds any new $\Pi_1$ theorems is an open
problem. So is whether every $\Delta_0$ formula is equivalent over $\mathsf{I}\Delta_0$, or over
$\mathsf{I}\Delta_0 + \Omega_1$, to a Diophantine formula; a positive answer would give
$\mathsf{NP} = \mathsf{coNP}$, as Wilkie observed.

- [DAq05, Question 8.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

/-- A Diophantine formula: a block of existential quantifiers over an open formula.
- [DAq05, Question 8.1] -/
inductive Semiformula.Diophantine {L : Language} {ξ : Type*} :
    {n : ℕ} → Semiformula L ξ n → Prop
  | of_open {n : ℕ} {φ : Semiformula L ξ n} : φ.Open → Diophantine φ
  | exs {n : ℕ} {φ : Semiformula L ξ (n + 1)} : Diophantine φ → Diophantine (∃¹ φ)

namespace Arithmetic

/-- $\mathsf{I}\Delta_0 + \Omega_1$ is $\Pi_1$-conservative over $\mathsf{I}\Delta_0$. An open
problem.
- [HP98, §V.1(a), p. 274]
- [HP98, §V.5(g), p. 395] -/
def ISigma0UnionOmega1WeakerThanOnPi1ISigma0 : Prop :=
  𝗜𝚺₀ ∪ 𝝮₁ ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ] 𝗜𝚺₀

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
