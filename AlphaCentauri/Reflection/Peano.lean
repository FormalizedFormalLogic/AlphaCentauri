module

public import AlphaCentauri.Reflection.ISigma
public import AlphaCentauri.ToFoundation.PrenexNormalForm

/-!
# `𝗣𝗔` proves the local reflection principle of `𝗜𝚺 n`

This is the Kreisel–Lévy theorem in its local form.
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment ProvabilityAbstraction

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
    ISigma.provable_localReflectionOn_Pi (k := s + n + 1) (by omega) (by omega) ⟨σ', hσ', rfl⟩
  have h₂ : 𝗣𝗔 ⊢ (𝗜𝚺 n).standardProvability σ 🡘 (𝗜𝚺 n).standardProvability σ' :=
    WeakerThan.pbl <| Provability.ext (𝔅 := (𝗜𝚺 n).standardProvability) he
  have h₃ : 𝗣𝗔 ⊢ σ 🡘 σ' := WeakerThan.pbl he
  cl_prover [h₁, h₂, h₃]

end FFL.FirstOrder.Arithmetic
