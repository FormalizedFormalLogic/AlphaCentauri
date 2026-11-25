module

public import AlphaCentauri.Model.BSigma

/-! # Strictness of the fragment hierarchy -/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic


section
variable (n : ℕ)

/-- $\mathsf{I}\Sigma_n$ is strictly weaker than $\mathsf{B}\Sigma_{n + 1}$.

- [HP98, Theorem IV.1.29(1)]
-/
theorem ISigma_strictlyWeakerThan_BSigma_succ : 𝗜𝚺 n ⪱ 𝗕𝚺 (n + 1) := by
  obtain ⟨M, _, _, a, ha⟩ := exists_model_nonstandard_sigmaDefinableElement
  have : (sigmaDefinableElements (n + 1) M)↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := sigmaDefinableElements.models_ISigma n
  constructor
  · exact ISigma_weakerThan_BSigma_succ
  · intro h
    exact sigmaDefinableElements.not_models_BSigma a
      (definableElementsOver_mono (fun _ hφ ↦ hφ.mono (by omega)) ha)
      (models_of_subtheory (T := 𝗕𝚺 (n + 1)) (U := 𝗜𝚺 n) this)

/-- $\mathsf{B}\Sigma_{n + 1}$ is strictly weaker than $\mathsf{I}\Sigma_{n + 1}$.

- [HP98, Theorem IV.1.29(1)]
- [Bus98A, Theorem 3.4.2]
-/
theorem BSigma_strictlyWeakerThan_ISigma : 𝗕𝚺 (n + 1) ⪱ 𝗜𝚺 (n + 1) := by
  obtain ⟨M, _, _, a, ha⟩ := exists_model_nonstandard_sigmaDefinableElement
  constructor
  · exact BSigma_weakerThan_ISigma
  · have ha' : (a : M) ∈ sigmaDefinableElements (n + 1) M :=
      definableElementsOver_mono (fun _ hφ ↦ hφ.mono (by omega)) ha
    intro h
    exact definableCut.not_models_ISigma a ha'
      (models_of_subtheory (T := 𝗜𝚺 (n + 1)) (U := 𝗕𝚺 (n + 1)) <|
        definableCut.models_BSigma (j := n) a)


end

end FFL.FirstOrder.Arithmetic
