module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import Foundation.FirstOrder.Incompleteness.Reflection.Uniform
public import AlphaCentauri.Bootstrapping.Proof.LocalReflection
public import AlphaCentauri.ToFoundation.PrenexNormalForm
public import AlphaCentauri.ToFoundation.Reflection

/-!
# Reflection principles proved by the fragments of arithmetic

For $n \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_n$ for prenex $\Pi_{k+3}$ sentences, and hence, for $k \ge 1$, that of
$\mathsf{I}\Sigma_k$ for all $\Sigma_1$ sentences. It also proves the uniform reflection principle
of $\mathsf{EA}$ for prenex $\Pi_{k+3}$ formulas. $\mathsf{PA}$ proves the local reflection
principle of every $\mathsf{I}\Sigma_n$ (the Kreisel–Lévy theorem).
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment ProvabilityAbstraction

variable {k m n : ℕ}

/-- For $n \le k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma_n$ for prenex $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
theorem ISigma.provable_localReflectionOn_Pi (hn : n ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3)] (𝗜𝚺 n) := by
  intro φ hφ
  obtain ⟨π, hπ, rfl⟩ := (Provability.mem_localReflectionOn_iff _).mp hφ
  apply Arithmetic.complete.{0}
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (s₁ := 1) (s₂ := k + 1) (by omega)
  simp only [Semantics.Imp.models_imply]
  intro hp
  have := Bootstrapping.models_of_provable_substNumerals
    (Bootstrapping.admitsFalseBlockReplacement_ISigma hn) hπ (![] : Fin 0 → V)
    (by simpa [models_iff, standardProvability_def] using hp)
  simpa [models_iff] using this

/-- $\mathsf{I}\Sigma_{k+1}$ proves the uniform reflection principle of $\mathsf{EA}$ for prenex
$\Pi_{k+3}$ formulas.
- [Bek05, Theorem 7]
- [Lei83] -/
theorem ISigma.provable_uniformReflectionOn_Pi_ElementaryArithmetic (k : ℕ) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3)] 𝗘𝗔 := by
  intro σ hσ
  obtain ⟨m, φ, hφ, rfl⟩ := mem_uniformReflectionOn_iff.mp hσ
  apply Arithmetic.complete.{0}
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := mod_ISigma_of_le (s₁ := 1) (s₂ := k + 1) (by omega)
  rw [models_iff, models_uniformReflectionSchema_iff]
  intro v hv
  exact Bootstrapping.models_of_provable_substNumerals
    Bootstrapping.admitsFalseBlockReplacement_ElementaryArithmetic hφ v hv

theorem ISigma.provable_localReflectionOn_prenexSigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 1] (𝗜𝚺 k) :=
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk
  provable_localReflectionOn_prenexHierarchy_of_lt (ISigma_weakerThan_of_le (by omega))
    (by omega) (ISigma.provable_localReflectionOn_Pi le_rfl)

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
    (ISigma.provable_localReflectionOn_Pi le_rfl)

theorem ISigma.provable_localReflectionOn_prenexPi (hn : 1 ≤ n) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 n] (𝗜𝚺 n) :=
  ISigma.provable_localReflectionOn_prenexPi_of_le hn (by omega)

/-- For every $n$, $\mathsf{PA}$ proves the local reflection principle of $\mathsf{I}\Sigma_n$.
- [HP98, Corollary I.4.34(3)] -/
theorem Peano.provable_localReflection_ISigma (n : ℕ) : 𝗣𝗔 ⊢* 𝗥𝗳𝗻[Set.univ] (𝗜𝚺 n) := by
  rintro _ ⟨σ, -, rfl⟩
  obtain ⟨s, hs⟩ := ℬ[<, ℒₒᵣ].exists_prenexHierarchy_eval_iff σ
  obtain ⟨σ', hσ', H⟩ := hs 𝚷 (s + n + 1 + 3) (by omega)
  have he : 𝗜𝚺 n ⊢ σ 🡘 σ' := by
    simpa using provable_iff_of_models_iff.{0} (n := 0) fun V _ _ e ↦ by
      simpa [models_iff] using H V e Empty.elim
  have h₁ : 𝗣𝗔 ⊢ (𝗜𝚺 n).standardProvability.refl σ' := WeakerThan.pbl <|
    ISigma.provable_localReflectionOn_Pi (k := s + n + 1) (by omega) ⟨σ', hσ', rfl⟩
  have h₂ : 𝗣𝗔 ⊢ (𝗜𝚺 n).standardProvability σ 🡘 (𝗜𝚺 n).standardProvability σ' :=
    WeakerThan.pbl <| Provability.ext (𝔅 := (𝗜𝚺 n).standardProvability) he
  have h₃ : 𝗣𝗔 ⊢ σ 🡘 σ' := WeakerThan.pbl he
  cl_prover [h₁, h₂, h₃]

end FFL.FirstOrder.Arithmetic
