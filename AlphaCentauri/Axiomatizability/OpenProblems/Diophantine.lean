module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata
import AlphaCentauri.OpenProblem

/-!
# Diophantine equivalents of $\Delta_0$ formulas

Whether every $\Delta_0$ formula is equivalent over $\mathsf{I}\Delta_0$, or over
$\mathsf{I}\Delta_0 + \Omega_1$, to a Diophantine formula is open. A positive answer would give
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

/-- Does $\mathsf{I}\Delta_0$ prove that every $\Delta_0$ formula is equivalent to a Diophantine
formula?
- [DAq05, Question 8.1] -/
open_problem exists_diophantine_equiv_ISigma0 :=
  ∀ φ : ArithmeticFormula ℕ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ →
    ∃ ψ : ArithmeticFormula ℕ, Semiformula.Diophantine ψ ∧ 𝗜𝚺₀ ⊢ (φ 🡘 ψ).univCl

/-- Does $\mathsf{I}\Delta_0 + \Omega_1$ prove that every $\Delta_0$ formula is equivalent to a
Diophantine formula?
- [DAq05, §8] -/
open_problem exists_diophantine_equiv_ISigma0_union_Omega1 :=
  ∀ φ : ArithmeticFormula ℕ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ →
    ∃ ψ : ArithmeticFormula ℕ, Semiformula.Diophantine ψ ∧ 𝗜𝚺₀ ∪ 𝝮₁ ⊢ (φ 🡘 ψ).univCl

end Arithmetic

end FFL.FirstOrder
