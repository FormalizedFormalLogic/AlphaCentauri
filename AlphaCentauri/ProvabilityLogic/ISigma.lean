module

public import AlphaCentauri.Axiomatizability.ISigma
public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.ProvabilityLogic.Reflection
public import Foundation.ProvabilityLogic.Classification.General

/-!
# The provability logic of `𝗜𝚺 m` relative to `𝗜𝚺 n`

For `1 ≤ m < n`, the provability logic of `𝗜𝚺 m` relative to `𝗜𝚺 n` is `𝐃`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

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


end FFL.ProvabilityLogic
