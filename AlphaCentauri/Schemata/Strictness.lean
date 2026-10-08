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

/-- $\mathsf{B}\Sigma_{n + 1}$ is strictly weaker than $\mathsf{I}\Sigma_{n + 1}$.

- [HP98, Theorem IV.1.29(1)]
- [Bus98A, Theorem 3.4.2]
-/
axiom BSigma_strictlyWeakerThan_ISigma (n : ℕ) : 𝗕𝚺 (n + 1) ⪱ 𝗜𝚺 (n + 1)

end FFL.FirstOrder.Arithmetic
