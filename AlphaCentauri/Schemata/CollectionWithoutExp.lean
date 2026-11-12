module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv
import AlphaCentauri.OpenProblem

/-! # $\Sigma_1$ collection without exponentiation

Whether $\mathsf{I}\Delta_0$ together with the failure of exponentiation proves
$\mathsf{B}\Sigma_1$ is open.

- [WP89]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


/-- $\mathsf{I}\Delta_0 + \neg\mathrm{Exp}$ proves $\mathsf{B}\Sigma_1$.
- [WP89] -/
open_problem BSigma1_weakerThan_ISigma0_union_not_exp := 𝗕𝚺 1 ⪯ 𝗜𝚺₀ ∪ {∼expAxiom}


end FFL.FirstOrder.Arithmetic
