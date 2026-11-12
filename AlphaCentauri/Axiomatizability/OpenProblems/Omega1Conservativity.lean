module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata
import AlphaCentauri.OpenProblem

/-!
# $\Pi_1$-conservativity of $\Omega_1$ over $\mathsf{I}\Delta_0$

Whether adjoining $\Omega_1$ to $\mathsf{I}\Delta_0$ adds any new $\Pi_1$ theorems is open.

- [HP98, §V.1(a), p. 274]
- [HP98, §V.5(g), p. 395]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder


/-- Is $\mathsf{I}\Delta_0 + \Omega_1$ $\Pi_1$-conservative over $\mathsf{I}\Delta_0$?
- [HP98, §V.1(a), p. 274]
- [HP98, §V.5(g), p. 395] -/
open_problem Arithmetic.ISigma0_union_Omega1_weakerThanOn_Pi1_ISigma0 :=
  𝗜𝚺₀ ∪ 𝝮₁ ⪯[fun σ ↦ ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ] 𝗜𝚺₀


end FFL.FirstOrder
