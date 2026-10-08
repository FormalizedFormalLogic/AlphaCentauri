module

public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-!
# Strictness of the fragment hierarchy
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- $\mathsf{I}\Sigma_n$ is strictly weaker than $\mathsf{B}\Sigma_{n + 1}$.

- [HP98, Theorem IV.1.29(1)]
-/
axiom ISigma_strictlyWeakerThan_BSigma_succ (n : ℕ) : 𝗜𝚺 n ⪱ 𝗕𝚺 (n + 1)

end FFL.FirstOrder.Arithmetic
