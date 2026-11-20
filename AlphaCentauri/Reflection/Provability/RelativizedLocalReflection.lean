module

public import AlphaCentauri.Reflection.Provability.Relativized
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.PrenexPairing
public import AlphaCentauri.ToFoundation.ProvabilityLogic.ProvabilityAbstraction

/-!
# Relativized local reflection

Local reflection for provability relativized to true $\Pi_n$ sentences. Restricted to
$\Sigma_{n + 1}$ sentences it proves its own restriction to Boolean combinations of
$\Sigma_{n + 1}$ sentences.

- [Bek99, §3]
- [Bek99, Lemma 4.3]
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁] (n : ℕ)

/-- Local reflection for `Prov^n_T`, restricted to the sentences satisfying `Γ`.
- [Bek99, §3] -/
abbrev _root_.FFL.FirstOrder.Theory.relativizedLocalReflectionOn
    (Γ : ArithmeticSentence → Prop) : Set ArithmeticSentence :=
  (T.relativizedProvability n).reflOn Γ

variable [𝗜𝚺₁ ⪯ T]

/-- Relativized local reflection for $\Sigma_{n + 1}$ sentences is equivalent to relativized local
reflection for Boolean combinations of $\Sigma_{n + 1}$ sentences.
- [Bek99, Lemma 4.3] -/
theorem relativizedLocalReflectionOn_booleanCombination_equiv :
    T ∪ T.relativizedLocalReflectionOn n (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 (n + 1)) ≊
      T ∪ T.relativizedLocalReflectionOn n
        (BooleanCombination (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 (n + 1))) := by
  apply Entailment.Equiv.antisymm
  constructor
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | hφ)
    · exact Axiomatized.by_axm (Set.mem_union_left _ hφ)
    · obtain ⟨σ, hσ, rfl⟩ := (Provability.mem_localReflectionOn_iff _).mp hφ
      exact Axiomatized.by_axm (Set.mem_union_right _
        ((Provability.mem_localReflectionOn_iff _).mpr ⟨σ, .pos hσ, rfl⟩))
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | hφ)
    · exact Axiomatized.by_axm (Set.mem_union_left _ hφ)
    · obtain ⟨σ, hσ, rfl⟩ := (Provability.mem_localReflectionOn_iff _).mp hφ
      have : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝚺₁ := inferInstance
      have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₁ := inferInstance
      exact provable_refl_of_booleanCombination
        (fun σ τ hσ hτ ↦ by simpa using hσ.exists_provable_iff_and 𝗜𝚺₁ hτ)
        (fun σ τ hσ hτ ↦ by simpa using hσ.exists_provable_iff_or 𝗜𝚺₁ hτ)
        (Bounding.PrenexHierarchy.exists_provable 𝗜𝚺₁)
        (Bounding.PrenexHierarchy.exists_refutable 𝗜𝚺₁)
        (T.relativizedProvability n)
        (fun _ h ↦ relativizedProvability_formalizedCompleteOn T h) hσ

end FFL.FirstOrder.Arithmetic
