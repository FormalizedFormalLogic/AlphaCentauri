module

public import AlphaCentauri.Reflection.UniformReflection.Induction
public import AlphaCentauri.Reflection.ISigma

/-!
# Leivant–Ono theorem

For $n \ge 1$, $\mathsf{I}\Sigma_n$ is equivalent to $\mathsf{EA}$ together with the uniform
reflection principle of $\mathsf{EA}$ for prenex $\Pi_{n + 2}$ formulas.

- [AB05, Theorem 154]
- [Bek05, Theorem 7]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment

variable {n : ℕ}

/-- A model of `𝗘𝗔` and of uniform prenex $\Pi_{n + 2}$ reflection for `𝗘𝗔` satisfies induction
for prenex $\Sigma_n$ formulas.
- [Bek05, Theorem 7] -/
lemma models_succInd_of_uniformReflection_ElementaryArithmetic {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗘𝗔] [V↓[ℒₒᵣ] ⊧* 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n φ) :
    V↓[ℒₒᵣ] ⊧ .univCl (succInd φ) := by
  obtain ⟨χ, rfl⟩ := hφ
  set ψ := χ.rew (χ.val.paramSubst ![#0])
  obtain ⟨θ, hθ, hθψ⟩ := exists_inductionImplication.{0} ψ
  simp only [models_iff, Semiformula.eval_univCl, succInd]
  simp only [LogicalConnective.HomClass.map_imply, Semiformula.eval_substs, Semiformula.eval_all,
    LogicalConnective.Prop.arrow_eq]
  intro f
  have hψ (x : V) :
      Semiformula.Eval (x :> fun i ↦ f i) Empty.elim ψ.val ↔ χ.val.Eval ![x] f :=
    (χ.val_rew _).symm ▸ Semiformula.eval_toSemisentence_one χ.val x f
  have hrfn : V ⊧/![] (𝗘𝗔.uniformReflectionSchema θ) :=
    models_iff.mp <| Semantics.ModelsSet.models _
      (show _ ∈ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 from ⟨_, θ, hθ, rfl⟩)
  intro h₀ hs x
  have hprov :=
    ElementaryArithmetic.Bootstrapping.provable_substNumerals_of_provable_zero_of_provable_succ
      (T := 𝗘𝗔) θ (provable_inductionImplication_zero hθψ) (provable_inductionImplication_succ hθψ)
      x (fun i ↦ f i)
  have h := (hθψ V Empty.elim x _).mp
    ((ElementaryArithmetic.models_uniformReflectionSchema_iff 𝗘𝗔 θ).mp hrfn _ hprov)
  simp only [hψ] at h
  simpa using h (by simpa using h₀) (by simpa using hs)

/-- $\mathsf{EA}$ together with the uniform reflection principle of $\mathsf{EA}$ for prenex
$\Pi_{n + 2}$ formulas proves $\mathsf{I}\Sigma_n$.
- [AB05, Theorem 154]
- [Bek05, Theorem 7] -/
theorem ISigma_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi (n : ℕ) :
    𝗜𝚺 n ⪯ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
    WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔) inferInstance
  weakerThan_of_models.{0} _ _ fun V _ hV ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗘𝗔 :=
      ModelsTheory.of_add_left V 𝗘𝗔 (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔)
    have : V↓[ℒₒᵣ] ⊧* 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
      ModelsTheory.of_add_right V 𝗘𝗔 (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔)
    simp only [Semantics.ModelsSet.union_iff, InductionScheme]
    and_intros
    · infer_instance
    · apply Semantics.ModelsSet.setOf_iff.mpr
      rintro _ ⟨φ, hφ, rfl⟩
      exact models_succInd_of_uniformReflection_ElementaryArithmetic hφ

/-- Uniform prenex $\Pi_{n + 2}$ reflection for `𝗘𝗔` over `𝗜𝚺₁` yields `𝗜𝚺 n`.
- [Bek05, Theorem 7] -/
theorem ISigma_weakerThan_ISigma1_union_uniformReflectionOn_Pi (n : ℕ) :
    𝗜𝚺 n ⪯ 𝗜𝚺₁ ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
  (ISigma_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi n).trans <|
    weakerThan_of_models.{0} _ _ fun V _ hV ↦ by
      have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
        ModelsTheory.of_add_left V 𝗜𝚺₁ (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔)
      exact Semantics.ModelsSet.union_iff.mpr
        ⟨ModelsTheory.of_provably_subtheory V 𝗘𝗔 𝗜𝚺₁ inferInstance,
          ModelsTheory.of_add_right V 𝗜𝚺₁ (𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔)⟩

/-- For $n \ge 1$, $\mathsf{EA}$ together with the uniform reflection principle of $\mathsf{EA}$ for
prenex $\Pi_{n + 2}$ formulas proves $\mathsf{I}\Sigma_1$.
- [AB05, Theorem 154]
- [Bek05, Theorem 7] -/
theorem ISigma1_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi (hn : 1 ≤ n) :
    𝗜𝚺₁ ⪯ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 :=
  ISigma_weakerThan_of_le_trans hn
    (ISigma_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi n)

/-- For $n \ge 1$, $\mathsf{I}\Sigma_n$ is equivalent to $\mathsf{EA}$ together with the uniform
reflection principle of $\mathsf{EA}$ for prenex $\Pi_{n + 2}$ formulas.
- [AB05, Theorem 154]
- [Bek05, Theorem 7] -/
theorem ISigma_equiv_uniformReflection_ElementaryArithmetic (hn : 1 ≤ n) :
    𝗜𝚺 n ≊ 𝗘𝗔 ∪ 𝗥𝗙𝗡[ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 (n + 2)] 𝗘𝗔 := by
  apply Equiv.antisymm
  constructor
  · exact ISigma_weakerThan_ElementaryArithmetic_union_uniformReflectionOn_Pi n
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | hφ)
    · exact (ISigma_weakerThan_of_le hn).pbl (WeakerThan.pbl (𝓢 := 𝗘𝗔) (by_axm hφ))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact ISigma.provable_uniformReflectionOn_Pi_ElementaryArithmetic k hφ

end FFL.FirstOrder.Arithmetic
