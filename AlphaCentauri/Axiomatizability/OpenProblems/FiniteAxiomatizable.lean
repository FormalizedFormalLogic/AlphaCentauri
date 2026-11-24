module

public import AlphaCentauri.ToFoundation.FirstOrder.Axiomatizability
public import AlphaCentauri.ToFoundation.FirstOrder.Theory
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
public import Foundation.FirstOrder.Arithmetic.Omega1.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata
import AlphaCentauri.OpenProblem

/-!
# Finite axiomatizability of the open cases

Open problems on finite axiomatizability of fragments of arithmetic.

- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Arithmetic

/-- Is $\mathsf{B}\Sigma_1$ finitely axiomatizable?
- [Kay91, Exercise 10.4] -/
open_problem BSigma1_finiteAxiomatizable := FiniteAxiomatizable (𝗕𝚺 1)

/-- Is $\mathsf{I}\Delta_0$ finitely axiomatizable?
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
open_problem ISigma0_finiteAxiomatizable := FiniteAxiomatizable 𝗜𝚺₀

/-- Is $\mathsf{I}\Delta_0 + \Omega_1$ finitely axiomatizable?
- [HP98, Corollary V.4.39]
- [Kay91, Exercise 10.4] -/
open_problem ISigma0_union_Omega1_finiteAxiomatizable := FiniteAxiomatizable (𝗜𝚺₀ ∪ 𝝮₁)

end Arithmetic

end FFL.FirstOrder
