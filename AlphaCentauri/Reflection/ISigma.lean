module

public import AlphaCentauri.Bootstrapping.Proof.LocalReflection
public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import AlphaCentauri.ToFoundation.Reflection
public import Foundation.FirstOrder.Incompleteness.Reflection.Uniform

/-!
# Reflection principles proved by the fragments of arithmetic

For $1 \le k$ and $n \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_n$ for prenex $\Pi_{k+3}$ sentences, and hence, for $k \ge 1$, that of
$\mathsf{I}\Sigma_k$ for all $\Sigma_1$ sentences. It also proves the uniform reflection principle
of $\mathsf{EA}$ for prenex $\Pi_{k+3}$ formulas.
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment ProvabilityAbstraction

variable {k m n : ℕ}

/-- For $1 \le k$ and $n \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_n$ for prenex $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
theorem ISigma.provable_localReflectionOn_Pi (hk : 1 ≤ k) (hn : n ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3)] (𝗜𝚺 n) := by
  intro φ hφ
  obtain ⟨π, hπ, rfl⟩ := (Provability.mem_localReflectionOn_iff _).mp hφ
  apply Arithmetic.complete.{0}
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (s₁ := 1) (s₂ := k + 1) (by omega)
  simp only [Semantics.Imp.models_imply]
  intro hp
  have := Bootstrapping.models_of_provable_substNumerals hk
    (Bootstrapping.admitsFalseBlockReplacement_ISigma hn) hπ (![] : Fin 0 → V)
    (by simpa [models_iff, standardProvability_def] using hp)
  simpa [models_iff] using this

/-- For $1 \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the uniform reflection principle of $\mathsf{EA}$
for prenex $\Pi_{k+3}$ formulas.
- [Bek05, Theorem 7]
- [Lei83] -/
theorem ISigma.provable_uniformReflectionOn_Pi_ElementaryArithmetic (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3)] 𝗘𝗔 := by
  intro σ hσ
  obtain ⟨m, φ, hφ, rfl⟩ := mem_uniformReflectionOn_iff.mp hσ
  apply Arithmetic.complete.{0}
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (s₁ := 1) (s₂ := k + 1) (by omega)
  rw [models_iff, models_uniformReflectionSchema_iff]
  intro v hv
  exact Bootstrapping.models_of_provable_substNumerals hk
    Bootstrapping.admitsFalseBlockReplacement_ElementaryArithmetic hφ v hv

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
