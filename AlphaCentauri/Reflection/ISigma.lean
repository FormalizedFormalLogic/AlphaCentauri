module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import AlphaCentauri.ToFoundation.Definability

/-!
# Local reflection between the fragments of arithmetic

`𝗜𝚺 (k + 1)` proves the local reflection principle of `𝗜𝚺 k` for strict $\Pi_{k+3}$ sentences.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- For every $k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_k$ for strict $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
axiom ISigma.provable_localReflectionOn_Pi (k : ℕ) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[StrictHierarchy 𝚷 (k + 3)] (𝗜𝚺 k)

end FFL.FirstOrder.Arithmetic
