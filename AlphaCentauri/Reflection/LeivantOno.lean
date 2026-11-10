module

public import AlphaCentauri.Reflection.InductionFromReflection
public import AlphaCentauri.Reflection.ISigma

/-!
# The Leivant–Ono theorem

For $n \ge 1$, $\mathsf{I}\Sigma_n$ is equivalent to $\mathsf{EA}$ together with the uniform
reflection principle of $\mathsf{EA}$ for prenex $\Pi_{n + 2}$ formulas.

- [AB05, Theorem 154]
- [Bek05, Theorem 7]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment

variable {n : ℕ}

/-- For $n \ge 1$, $\mathsf{EA}$ together with the uniform reflection principle of $\mathsf{EA}$ for
prenex $\Pi_{n + 2}$ formulas proves $\mathsf{I}\Sigma_1$.
- [AB05, Theorem 154]
- [Bek05, Theorem 7] -/
axiom ISigma1_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi (hn : 1 ≤ n) :
    𝗜𝚺₁ ⪯ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔

/-- For $n \ge 1$, $\mathsf{I}\Sigma_n$ is equivalent to $\mathsf{EA}$ together with the uniform
reflection principle of $\mathsf{EA}$ for prenex $\Pi_{n + 2}$ formulas.
- [AB05, Theorem 154]
- [Bek05, Theorem 7] -/
theorem ISigma_equiv_uniformReflection_ElementaryArithmetic (hn : 1 ≤ n) :
    𝗜𝚺 n ≊ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 := by
  apply Equiv.antisymm
  constructor
  · apply (ISigma_weakerThan_ISigma1_union_uniformReflectionOn_Pi n).trans
    apply WeakerThan.ofAxm!
    rintro φ (hφ | hφ)
    · exact (ISigma1_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi hn).pbl
        (by_axm hφ)
    · exact by_axm (Set.mem_union_right _ hφ)
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | hφ)
    · exact (ISigma_weakerThan_of_le hn).pbl (WeakerThan.pbl (𝓢 := 𝗘𝗔) (by_axm hφ))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact ISigma.provable_uniformReflectionOn_Pi_ElementaryArithmetic k hφ

theorem ISigma1_equiv_uniformReflection_ElementaryArithmetic :
    𝗜𝚺 1 ≊ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 3] 𝗘𝗔 :=
  ISigma_equiv_uniformReflection_ElementaryArithmetic le_rfl

theorem ISigma2_equiv_uniformReflection_ElementaryArithmetic :
    𝗜𝚺 2 ≊ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 4] 𝗘𝗔 :=
  ISigma_equiv_uniformReflection_ElementaryArithmetic (by norm_num)

end FFL.FirstOrder.Arithmetic
