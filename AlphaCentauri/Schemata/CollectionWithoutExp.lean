module

public import Foundation.FirstOrder.Arithmetic.EA.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-! # $\Sigma_1$ collection without exponentiation

Whether $\mathsf{I}\Delta_0$ together with the failure of exponentiation proves
$\mathsf{B}\Sigma_1$ is open.

- [WP89]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section CollectionWithoutExp

/-- $\mathsf{I}\Delta_0 + \neg\mathrm{Exp}$ proves $\mathsf{B}\Sigma_1$. An open problem.
- [WP89] -/
def BSigma1WeakerThanISigma0AddNotExp : Prop := 𝗕𝚺 1 ⪯ 𝗜𝚺₀ ∪ {∼expAxiom}

end CollectionWithoutExp

end FFL.FirstOrder.Arithmetic
