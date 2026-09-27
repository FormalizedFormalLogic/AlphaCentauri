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

variable {k m n : ℕ}

/-- For every $k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_k$ for strict $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
axiom ISigma.provable_localReflectionOn_Pi (k : ℕ) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[StrictHierarchy 𝚷 (k + 3)] (𝗜𝚺 k)

/--
- [HP98, Corollary I.4.34(3)] -/
theorem ISigma.provable_localReflectionOn_stSigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[StrictHierarchy 𝚺 1] (𝗜𝚺 k) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk;
  intro φ hφ;
  apply provable_localReflectionOn_Pi;
  exact Provability.localReflectionOn_mono _ (fun _ h ↦ h.strict_mono 𝚷 (by omega)) hφ


/--
- [HP98, Corollary I.4.34(3)] -/
theorem ISigma.provable_localReflectionOn_Sigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] (𝗜𝚺 k) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk;
  apply provable_localReflectionOn_hierarchy_of_strictHierarchy;
  · exact ISigma_weakerThan_of_le (by omega);
  · exact ISigma.provable_localReflectionOn_stSigma1 hk;

/--
- [HP98, Corollary I.4.34(3)] -/
theorem ISigma.provable_localReflectionOn_Sigma1_of_lt (hm : 1 ≤ m) (hmn : m < n) :
    𝗜𝚺 n ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] (𝗜𝚺 m) := fun hσ ↦
  (ISigma_weakerThan_of_le hmn).pbl (ISigma.provable_localReflectionOn_Sigma1 hm hσ)

end FFL.FirstOrder.Arithmetic
