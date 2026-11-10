module

public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.ProvabilityLogic.Classification.Truth
public import AlphaCentauri.Axiomatizability.ISigma
public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.Entailment
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection

/-!
# Provability logics of fragments of arithmetic

For $n \ge 1$, the provability logic of $\mathsf{I}\Sigma_n$ relative to $\mathsf{PA}$ is
$\mathbf{S}$. For $1 \le m < n$, the provability logic of $\mathsf{I}\Sigma_m$ relative to
$\mathsf{I}\Sigma_n$ is $\mathbf{D}$. The provability logic of $\mathsf{I}\Sigma_1$ relative to
$\mathsf{I}\Sigma_1 + \mathrm{Con}(\mathsf{PA})$ is $\mathbf{A}$.

- [AB05, Example 61]
- [AB05, Example 62]
- [AB05, Example 63]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {n : ℕ}

/-- For $n \ge 1$, the provability logic of $\mathsf{I}\Sigma_n$ relative to $\mathsf{PA}$ is
$\mathbf{S}$.
- [AB05, Example 61] -/
theorem provabilityLogic_ISigma_Peano_eq_S (hn : 1 ≤ n) :
    (𝗜𝚺 n).provabilityLogicRelativeTo 𝗣𝗔 (α := α) = 𝐒 := by
  set L := (𝗜𝚺n).provabilityLogicRelativeTo 𝗣𝗔;
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le hn
  apply Logic.weakerThan_antisymm;
  · suffices L ⪯ (𝗜𝚺n).provabilityLogicRelativeTo 𝗧𝗔 by
      rwa [Logic.S.eq_provabilityLogicRelativeTo_TA (T := 𝗜𝚺 n)];
    constructor;
    intro A hA f;
    exact (inferInstance : 𝗣𝗔 ⪯ 𝗧𝗔).pbl (hA f);
  · exact S_weakerThan_provabilityLogic_of_provable_localReflection
      <| Peano.provable_localReflection_ISigma n

open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {m n : ℕ}

/-- For $1 \le m < n$, the trace of the provability logic of $\mathsf{I}\Sigma_m$ relative to
$\mathsf{I}\Sigma_n$ is `ω`. -/
lemma trace_provabilityLogic_ISigma_ISigma_eq_univ (hm : 1 ≤ m) (hmn : m < n) :
    ((𝗜𝚺 m).provabilityLogicRelativeTo (𝗜𝚺 n) (α := α)).trace = .univ := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 m := ISigma_weakerThan_of_le (by omega)
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le (by omega)
  exact trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1
    (ISigma.provable_localReflectionOn_Sigma1_of_lt hm hmn)

/-- For $1 \le m < n$, `𝐃` is weaker than the provability logic of $\mathsf{I}\Sigma_m$ relative
to $\mathsf{I}\Sigma_n$. -/
lemma D_weakerThan_provabilityLogic_ISigma_ISigma (hm : 1 ≤ m) (hmn : m < n) :
    𝐃 ⪯ (𝗜𝚺 m).provabilityLogicRelativeTo (𝗜𝚺 n) (α := α) := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 m := ISigma_weakerThan_of_le (by omega)
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le (by omega)
  exact D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (ISigma.provable_localReflectionOn_Sigma1_of_lt hm hmn)

/-- For $1 \le m < n$, the provability logic of $\mathsf{I}\Sigma_m$ relative to
$\mathsf{I}\Sigma_n$ is $\mathbf{D}$.
- [AB05, Example 62] -/
theorem provabilityLogic_ISigma_ISigma_eq_D (hm : 1 ≤ m) (hmn : m < n) :
    (𝗜𝚺 m).provabilityLogicRelativeTo (𝗜𝚺 n) (α := α) = 𝐃 := by
  set L := (𝗜𝚺 m).provabilityLogicRelativeTo (𝗜𝚺 n) (α := α);
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 m := ISigma_weakerThan_of_le (by omega)
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le (by omega)
  apply Logic.weakerThan_antisymm;
  · -- (ii) a provability logic strictly above `𝐃` would give a consistent extension of `𝗜𝚺 m` by
    -- a single sentence that proves its full local reflection schema, contradiction.
    by_contra! h;
    obtain ⟨-, A, hAD, hA⟩ := strictlyWeakerThan_iff.mp (
      ⟨D_weakerThan_provabilityLogic_ISigma_ISigma hm hmn, ‹_›⟩ : 𝐃 ⪱ L
    );
    obtain ⟨π, hπ⟩ := ISigma.exists_pi_axiomatization_insert n (by omega) m (by omega)
    have : Consistent (insert π.val (𝗜𝚺 m)) :=
      (Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], inferInstance⟩ : Consistent (𝗜𝚺 n)).of_le
        hπ.symm.le
    apply not_provable_localReflectionOn_univ_insert (T := 𝗜𝚺 m) (π := π.val) this;
    rintro _ ⟨σ, -, rfl⟩;
    exact hπ.le.pbl <| provable_reflection_of_not_D
      (trace_provabilityLogic_ISigma_ISigma_eq_univ hm hmn) hA hAD
  · exact D_weakerThan_provabilityLogic_ISigma_ISigma hm hmn;


open Entailment FirstOrder FirstOrder.Arithmetic

variable {α : Type*}

/-- The provability logic of `𝗜𝚺₁` relative to `𝗜𝚺₁ + Con(𝗣𝗔)` is `𝐀`.
- [AB05, Example 63] -/
theorem provabilityLogic_ISigma1_add_con_Peano_eq_A :
    (𝗜𝚺₁).provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗣𝗔.Con) (α := α) = 𝐀 := by
  apply provabilityLogic_add_con_eq_A;
  · exact InductionOnPrenexHierarchy.provable_standardProvability_imp_Peano 1;
  · intro σ hσ;
    exact (inferInstance : 𝗜𝚺 2 ⪯ 𝗣𝗔).pbl (ISigma.provable_localReflectionOn_Sigma1 le_rfl hσ)
  · apply Theory.consistent_of_satisfiable ⟨ℕ↓[ℒₒᵣ], ?_⟩;
    apply Semantics.modelsSet_iff.mpr;
    rintro φ (hφ | rfl)
    · exact Semantics.modelsSet_iff.mp inferInstance hφ
    · simp [models_iff]

end FFL.ProvabilityLogic
