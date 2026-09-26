module

public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.Hierarchy
public import AlphaCentauri.ToFoundation.StandardProvability

/-!
# `𝗣𝗔` proves the local reflection principle of `𝗜𝚺 n`

This is the Kreisel–Lévy theorem in its local form.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment ProvabilityAbstraction

/-- For every $n$, $\mathsf{PA}$ proves the local reflection principle of $\mathsf{I}\Sigma_n$.
- [HP98, Corollary I.4.34(3)] -/
theorem Peano.provable_localReflection_ISigma (n : ℕ) : 𝗣𝗔 ⊢* 𝗥𝗳𝗻[Set.univ] (𝗜𝚺 n) := by
  rintro _ ⟨σ, -, rfl⟩
  obtain ⟨k, hk⟩ := Hierarchy.exists_forall_hierarchy σ
  obtain ⟨j, hnj, hkj, hj⟩ : ∃ j, n ≤ j ∧ k ≤ j ∧ 1 ≤ j := ⟨n + k + 1, by omega, by omega, by omega⟩
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 j := ISigma_weakerThan_of_le hj
  have h₁ : 𝗜𝚺 (j + 1) ⊢* 𝗥𝗳𝗻[Hierarchy 𝚷 j] (𝗜𝚺 j) := by
    apply provable_localReflectionOn_hierarchy_of_strictHierarchy
      (ISigma_weakerThan_of_le (by omega))
    intro φ hφ
    exact ISigma.provable_localReflectionOn_Pi j <|
      Provability.localReflectionOn_mono _ (fun _ h ↦ h.mono (by omega)) hφ
  have h₂ : 𝗜𝚺 (j + 1) ⊢ (𝗜𝚺 j).standardProvability σ 🡒 σ := h₁ ⟨σ, (hk 𝚷).mono hkj, rfl⟩
  have h₃ : 𝗜𝚺 (j + 1) ⊢ (𝗜𝚺 n).standardProvability σ 🡒 (𝗜𝚺 j).standardProvability σ :=
    (ISigma_weakerThan_of_le (by omega)).pbl <| ISigma.provable_standardProvability_imp_of_le hnj σ
  exact (inferInstance : 𝗜𝚺 (j + 1) ⪯ 𝗣𝗔).pbl <| C_trans h₃ h₂

end FFL.FirstOrder.Arithmetic
