module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import AlphaCentauri.ToFoundation.Definability

/-!
# Local reflection between the fragments of arithmetic

`𝗜𝚺 (k + 1)` proves the local reflection principle of `𝗜𝚺 k` for strict $\Pi_{k+3}$ sentences,
and hence, for `k ≥ 1`, for all $\Sigma_1$ sentences.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ProvabilityAbstraction

/-- For every $k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_k$ for strict $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
axiom ISigma.provable_localReflectionOn_Pi (k : ℕ) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[StrictHierarchy 𝚷 (k + 3)] (𝗜𝚺 k)

/-- For $k \ge 1$, $\mathsf{I}\Sigma_{k+1}$ proves the local $\Sigma_1$ reflection principle of
$\mathsf{I}\Sigma_k$.
- [HP98, Corollary I.4.34(3)] -/
theorem ISigma.provable_localReflectionOn_Sigma1 {k : ℕ} (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] (𝗜𝚺 k) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk
  apply provable_localReflectionOn_hierarchy_of_strictHierarchy (ISigma_weakerThan_of_le (by omega))
  intro φ hφ
  exact ISigma.provable_localReflectionOn_Pi k <|
    Provability.localReflectionOn_mono _ (fun _ h ↦ h.strict_mono 𝚷 (by omega)) hφ

end FFL.FirstOrder.Arithmetic
