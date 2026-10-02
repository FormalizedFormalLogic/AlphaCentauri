module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local
public import AlphaCentauri.ToFoundation.Reflection
public import AlphaCentauri.ToFoundation.StandardProvability

/-!
# Local reflection between the fragments of arithmetic

`𝗜𝚺 (k + 1)` proves the local reflection principle of `𝗜𝚺 k` for prenex $\Pi_{k+3}$ sentences,
and hence, for `k ≥ 1`, for all $\Sigma_1$ sentences.
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment ProvabilityAbstraction

variable {k m n : ℕ}

/-- For every $k$, $\mathsf{I}\Sigma_{k+1}$ proves the local reflection principle of
$\mathsf{I}\Sigma^+_k$ for prenex $\Pi_{k+3}$ sentences.
- [HP98, Corollary I.4.34(3)] -/
axiom ISigma.provable_localReflectionOn_Pi (k : ℕ) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (k + 3)] (𝗜𝚺⁺ k)

lemma provable_localReflectionOn_ISigma_of_IBroadSigma {S : ArithmeticTheory} [𝗜𝚺₁ ⪯ S]
    {C : ArithmeticSentence → Prop} (h : S ⊢* 𝗥𝗳𝗻[C] (𝗜𝚺⁺k)) : S ⊢* 𝗥𝗳𝗻[C] (𝗜𝚺 k) := by
  rintro _ ⟨σ, hσ, rfl⟩
  have h₁ := h ((Provability.mem_localReflectionOn_iff _).mpr ⟨σ, hσ, rfl⟩)
  have h₂ : S ⊢ (𝗜𝚺 k).standardProvability σ 🡒 (𝗜𝚺⁺ k).standardProvability σ :=
    (inferInstance : 𝗜𝚺₁ ⪯ S).pbl
      (InductionOnPrenexHierarchy.provable_standardProvability_imp_InductionOnHierarchy 𝚺 k σ)
  exact C_trans h₂ h₁

theorem ISigma.provable_localReflectionOn_prenexSigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 1] (𝗜𝚺 k) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺⁺ k := this.trans (ISigma_equiv_IBroadSigma k).le
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 (k + 1) := ISigma_weakerThan_of_le (by omega)
  apply provable_localReflectionOn_ISigma_of_IBroadSigma
  exact provable_localReflectionOn_prenexHierarchy_of_lt (T := 𝗜𝚺⁺ k)
    ((ISigma_equiv_IBroadSigma k).symm.le.trans (ISigma_weakerThan_of_le (by omega)))
    (by omega) (ISigma.provable_localReflectionOn_Pi k)

theorem ISigma.provable_localReflectionOn_Sigma1 (hk : 1 ≤ k) :
    𝗜𝚺 (k + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] (𝗜𝚺 k) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 k := ISigma_weakerThan_of_le hk
  apply provable_localReflectionOn_hierarchy_of_prenexHierarchy
  · exact ISigma_weakerThan_of_le (by omega)
  · exact ISigma.provable_localReflectionOn_prenexSigma1 hk

theorem ISigma.provable_localReflectionOn_Sigma1_of_lt (hm : 1 ≤ m) (hmn : m < n) :
    𝗜𝚺 n ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] (𝗜𝚺 m) := fun hσ ↦
  (ISigma_weakerThan_of_le hmn).pbl (ISigma.provable_localReflectionOn_Sigma1 hm hσ)

theorem IBroadSigma.provable_localReflectionOn_prenexPi_of_le (hn : 1 ≤ n) (hm : m ≤ n + 3) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m] (𝗜𝚺⁺ n) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺⁺ n := this.trans (ISigma_equiv_IBroadSigma n).le
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 (n + 1) := ISigma_weakerThan_of_le (by omega)
  intro φ hφ
  exact provable_localReflectionOn_prenexHierarchy_of_le (T := 𝗜𝚺⁺ n) (s := m) (s' := n + 3)
    ((ISigma_equiv_IBroadSigma n).symm.le.trans (ISigma_weakerThan_of_le (by omega)))
    hm (ISigma.provable_localReflectionOn_Pi n) hφ

theorem IBroadSigma.provable_localReflectionOn_Pi_self (hn : 1 ≤ n) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n] (𝗜𝚺⁺ n) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺⁺ n := this.trans (ISigma_equiv_IBroadSigma n).le
  have : 𝗜𝚺 1 ⪯ 𝗜𝚺⁺ n := ISigma_weakerThan_of_le hn |>.trans (ISigma_equiv_IBroadSigma n).le
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 (n + 1) := ISigma_weakerThan_of_le (by omega)
  intro φ hφ
  exact provable_localReflectionOn_hierarchy_of_prenexHierarchy
    ((ISigma_equiv_IBroadSigma n).symm.le.trans (ISigma_weakerThan_of_le (by omega)))
    (IBroadSigma.provable_localReflectionOn_prenexPi_of_le (m := n) hn (by omega)) hφ

theorem ISigma.provable_localReflectionOn_prenexPi_of_le (hn : 1 ≤ n) (hm : m ≤ n + 3) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 m] (𝗜𝚺 n) :=
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 (n + 1) := ISigma_weakerThan_of_le (by omega)
  provable_localReflectionOn_ISigma_of_IBroadSigma <|
    IBroadSigma.provable_localReflectionOn_prenexPi_of_le hn hm

theorem ISigma.provable_localReflectionOn_prenexPi (hn : 1 ≤ n) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 n] (𝗜𝚺 n) :=
  ISigma.provable_localReflectionOn_prenexPi_of_le hn (by omega)

theorem ISigma.provable_localReflectionOn_Pi_self (hn : 1 ≤ n) :
    𝗜𝚺 (n + 1) ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚷 n] (𝗜𝚺 n) :=
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 (n + 1) := ISigma_weakerThan_of_le (by omega)
  provable_localReflectionOn_ISigma_of_IBroadSigma <|
    IBroadSigma.provable_localReflectionOn_Pi_self hn

end FFL.FirstOrder.Arithmetic
