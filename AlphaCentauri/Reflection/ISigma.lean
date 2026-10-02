module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import AlphaCentauri.ToFoundation.Reflection

/-!
# Local reflection between the fragments of arithmetic

For $1 \le k$ and $n \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_n$ for prenex $\Pi_{k+3}$ sentences, and hence, for $k \ge 1$, that of
$\mathsf{I}\Sigma_k$ for all $\Sigma_1$ sentences.
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment ProvabilityAbstraction

variable {k m n : ℕ}

/-- For $1 \le k$ and $n \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_n$ for prenex $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
axiom ISigma.provable_localReflectionOn_Pi (hk : 1 ≤ k) (hn : n ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3)] (𝗜𝚺 n)

theorem ISigma.provable_localReflectionOn_prenexSigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 1] (𝗜𝚺 k) :=
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk
  provable_localReflectionOn_prenexHierarchy_of_lt (ISigma_weakerThan_of_le (by omega))
    (by omega) (ISigma.provable_localReflectionOn_Pi hk le_rfl)

theorem ISigma.provable_localReflectionOn_Sigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] (𝗜𝚺 k) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk
  apply provable_localReflectionOn_hierarchy_of_prenexHierarchy
  · exact ISigma_weakerThan_of_le (by omega)
  · exact ISigma.provable_localReflectionOn_prenexSigma1 hk

theorem ISigma.provable_localReflectionOn_Sigma1_of_lt (hm : 1 ≤ m) (hmn : m < n) :
    𝗜𝚺 n ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] (𝗜𝚺 m) := fun hσ ↦
  (ISigma_weakerThan_of_le hmn).pbl (ISigma.provable_localReflectionOn_Sigma1 hm hσ)

theorem ISigma.provable_localReflectionOn_prenexPi_of_le (hn : 1 ≤ n) (hm : m ≤ n + 3) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m] (𝗜𝚺 n) :=
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  provable_localReflectionOn_prenexHierarchy_of_le (ISigma_weakerThan_of_le (by omega)) hm
    (ISigma.provable_localReflectionOn_Pi hn le_rfl)

theorem ISigma.provable_localReflectionOn_prenexPi (hn : 1 ≤ n) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 n] (𝗜𝚺 n) :=
  ISigma.provable_localReflectionOn_prenexPi_of_le hn (by omega)

theorem ISigma.provable_localReflectionOn_Pi_self (hn : 1 ≤ n) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n] (𝗜𝚺 n) :=
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  provable_localReflectionOn_hierarchy_of_prenexHierarchy (ISigma_weakerThan_of_le (by omega))
    (ISigma.provable_localReflectionOn_prenexPi hn)

end FFL.FirstOrder.Arithmetic
