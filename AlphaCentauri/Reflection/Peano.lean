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
  rintro _ ⟨σ, -, rfl⟩;
  obtain ⟨k, hk⟩ := Bounding.Hierarchy.exists_forall_hierarchy σ;
  set j := n + k + 1;
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 j := ISigma_weakerThan_of_le (by omega);
  apply (inferInstance : 𝗜𝚺 (j + 1) ⪯ 𝗣𝗔).pbl;
  apply C_trans (ψ := (𝗜𝚺 j).standardProvability σ);
  · exact (ISigma_weakerThan_of_le (by omega)).pbl <|
      ISigma.provable_standardProvability_imp_of_le (by omega) σ;
  · apply ISigma.provable_localReflectionOn_Pi_self (by omega);
    simp only [Provability.mem_localReflectionOn_iff, Semiformula.imp_inj,
      exists_eq_right_right', and_true];
    apply (hk 𝚷).mono (by omega);

end FFL.FirstOrder.Arithmetic
