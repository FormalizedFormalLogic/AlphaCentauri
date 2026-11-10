module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Open problems on $\mathsf{I}\Delta_0$ and $\Omega_1$

Whether $\mathsf{B}\Sigma_1$, $\mathsf{I}\Delta_0$, or $\mathsf{I}\Delta_0 + \Omega_1$ is finitely
axiomatizable is open; $\mathsf{B}\Sigma_{n + 1}$ is finitely axiomatizable for $n \ge 1$, and
$\mathsf{I}\Delta_0$ and $\mathsf{I}\Delta_0 + \Omega_1$ are not if the polynomial hierarchy does
not collapse. It is also open whether $\mathsf{I}\Delta_0$ has a consistent complete extension
axiomatized by $\Sigma_n$ sentences for some $n$.

Whether adjoining $\Omega_1$ to $\mathsf{I}\Delta_0$ adds any new $\Pi_1$ theorems is also open.
So is whether every $\Delta_0$ formula is equivalent over $\mathsf{I}\Delta_0$, or over
$\mathsf{I}\Delta_0 + \Omega_1$, to a Diophantine formula; a positive answer would give
$\mathsf{NP} = \mathsf{coNP}$, as Wilkie observed.

- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4]
- [ELV25, Question 1.2]
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

/-- $\mathsf{B}\Sigma_1$ is finitely axiomatizable. An open problem.
- [Kay91, Exercise 10.4] -/
def BSigma1FiniteAxiomatizable : Prop := FiniteAxiomatizable (𝗕𝚺 1)

/-- $\mathsf{I}\Delta_0$ is finitely axiomatizable. An open problem.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
def ISigma0FiniteAxiomatizable : Prop := FiniteAxiomatizable 𝗜𝚺₀

/-- $\mathsf{I}\Delta_0 + \Omega_1$ is finitely axiomatizable. An open problem.
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
def ISigma0UnionOmega1FiniteAxiomatizable : Prop := FiniteAxiomatizable (𝗜𝚺₀ ∪ 𝝮₁)

/-- $\mathsf{I}\Delta_0$ has a consistent complete extension axiomatized by $\Sigma_n$ sentences
for some $n$. An open problem.
- [ELV25, Question 1.2] -/
def ExistsCompleteExtensionISigma0OfRestrictedComplexity : Prop :=
  ∃ (n : ℕ) (U : ArithmeticTheory), (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n σ) ∧
    𝗜𝚺₀ ⪯ U ∧ Entailment.Consistent U ∧ Entailment.Complete U


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
