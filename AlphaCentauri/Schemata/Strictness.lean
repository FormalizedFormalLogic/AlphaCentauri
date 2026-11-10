module

public import AlphaCentauri.Model.DefinableCut
public import AlphaCentauri.Model.DefinableElements

/-! # Strictness of the fragment hierarchy -/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section Strictness

/-- $\mathsf{I}\Sigma_n$ is strictly weaker than $\mathsf{B}\Sigma_{n + 1}$.

- [HP98, Theorem IV.1.29(1)]
-/
theorem ISigma_strictlyWeakerThan_BSigma_succ (n : ℕ) : 𝗜𝚺 n ⪱ 𝗕𝚺 (n + 1) := by
  obtain ⟨M, _, _, a, ha, hns⟩ := exists_model_nonstandard_definableElement
  have : (definableElements (n + 1) M)↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := definableElements.models_ISigma n
  constructor
  · exact ISigma_weakerThan_BSigma_succ
  intro h
  exact definableElements.not_models_BSigma (definableElements_mono (by omega) ha) hns
    (models_of_subtheory (T := 𝗕𝚺 (n + 1)) (U := 𝗜𝚺 n) this)

/-- $\mathsf{B}\Sigma_{n + 1}$ is strictly weaker than $\mathsf{I}\Sigma_{n + 1}$.

- [HP98, Theorem IV.1.29(1)]
- [Bus98A, Theorem 3.4.2]
-/
theorem BSigma_strictlyWeakerThan_ISigma (n : ℕ) : 𝗕𝚺 (n + 1) ⪱ 𝗜𝚺 (n + 1) := by
  obtain ⟨M, _, _, a, ha, hns⟩ := exists_model_nonstandard_definableElement
  have ha' := definableElements_mono (k' := n + 1) (by omega) ha
  have := definableCut.models_BSigma (j := n) hns
  constructor
  · exact BSigma_weakerThan_ISigma
  intro h
  exact definableCut.not_models_ISigma ha' hns
    (models_of_subtheory (T := 𝗜𝚺 (n + 1)) (U := 𝗕𝚺 (n + 1)) this)

end Strictness

end FFL.FirstOrder.Arithmetic
