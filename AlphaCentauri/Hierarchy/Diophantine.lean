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

/-- An open problem: $\mathsf{I}\Delta_0$ proves that every $\Delta_0$ formula is equivalent to a
Diophantine formula.
- [DAq05, Question 8.1] -/
axiom exists_diophantine_equiv_ISigma0 {φ : ArithmeticFormula ℕ}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) :
    ∃ ψ : ArithmeticFormula ℕ, Semiformula.Diophantine ψ ∧ 𝗜𝚺₀ ⊢ (φ 🡘 ψ).univCl

/-- An open problem: $\mathsf{I}\Delta_0 + \Omega_1$ proves that every $\Delta_0$ formula is
equivalent to a Diophantine formula.
- [DAq05, §8] -/
axiom exists_diophantine_equiv_ISigma0_union_Omega1 {φ : ArithmeticFormula ℕ}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) :
    ∃ ψ : ArithmeticFormula ℕ, Semiformula.Diophantine ψ ∧ 𝗜𝚺₀ ∪ 𝝮₁ ⊢ (φ 🡘 ψ).univCl

end Arithmetic

end FFL.FirstOrder
