module

public import AlphaCentauri.Axiomatizability.ISigma.Finite
public import AlphaCentauri.ToFoundation.FirstOrder.Hierarchy

/-!
# Single $\Pi$-axiomatizations of `𝗜𝚺 n`

The axioms of the finite theory of `𝗜𝚺 n` are $\Pi_{n + 3}$ sentences, so `𝗜𝚺 n` is axiomatized by
a single $\Pi_{n + 2}$ sentence for `n ≥ 1`, and by `𝗜𝚺 m` together with such a sentence for
`m ≤ n`.

## References

- [HP98, Corollary I.4.34(1)]
- [HP98, Remark I.4.35(1)]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping
open _root_.FFL.Entailment

namespace ISigma

variable {n : ℕ}

/-! ## The level of the finite theory in the arithmetical hierarchy -/

section Hierarchy

variable {n : ℕ}

/-! The induction and the collection axiom are universal closures of Boolean combinations of
formulas of level at most $\Sigma_{n + 1}$, so `Bounding.Hierarchy.iff_iff` splits the
biconditionals and `Bounding.Hierarchy.dummy_sigma`, `Bounding.Hierarchy.dummy_pi` absorb the
quantifier blocks that raise the level by one. -/
attribute [local simp] Bounding.Hierarchy.iff_iff Bounding.Hierarchy.dummy_sigma
  Bounding.Hierarchy.dummy_pi

@[simp]
lemma hierarchy_indSentence : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (n + 3) (indSentence n) := by
  have h₂ : ∀ Γ : Polarity, ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 2) (indFormula n) :=
    fun _ ↦ hierarchy_indFormula.strict_mono _ (by omega)
  have h₃ : ∀ Γ : Polarity, ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 3) (indFormula n) :=
    fun _ ↦ hierarchy_indFormula.strict_mono _ (by omega)
  simp [indSentence, succInd, h₂, h₃]

@[simp]
lemma hierarchy_collSentence : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (n + 3) (collSentence n) := by
  have h₂ : ∀ Γ : Polarity, ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 2) (collFormula n) := fun _ ↦
    hierarchy_collFormula.strict_mono _ (by omega)
  have h₃ : ∀ Γ : Polarity, ℬ[<, ℒₒᵣ].Hierarchy Γ (n + 3) (collFormula n) := fun _ ↦
    hierarchy_collFormula.strict_mono _ (by omega)
  simp [collSentence, collectionAxiom, h₂, h₃]

/-- Every axiom of the finite theory is $\Pi_{n + 3}$.
- [HP98, Corollary I.4.34(1)] -/
lemma hierarchy_of_mem_finiteAxiomatization {σ : ArithmeticSentence}
    (hσ : σ ∈ finiteAxiomatization n) : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (n + 3) σ := by
  rcases hσ with (hσ | hσ) | rfl | rfl
  · exact (Bounding.Hierarchy.of_mem_peanoMinus hσ).mono (by omega)
  · exact hierarchy_of_tarski hσ
  · exact hierarchy_indSentence
  · exact hierarchy_collSentence

end Hierarchy

/-- For `n ≥ 1`, `𝗜𝚺 n` is axiomatized by a single $\Pi_{n + 2}$ sentence.
- [HP98, Corollary I.4.34(1)]
- [HP98, Remark I.4.35(1)] -/
theorem exists_pi_axiomatization (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ : 𝚷ᴬ_[n + 2].Sentence, ({σ.val} : ArithmeticTheory) ≊ 𝗜𝚺 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := finiteAxiomatizableBy m
  have hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 (m + 1 + 2) h.conj := by
    rw [show m + 1 + 2 = m + 3 by omega, FiniteAxiomatizableBy.conj, Finset.conj]
    simpa using fun σ hσ ↦ hierarchy_of_mem_finiteAxiomatization (by simpa using hσ)
  exact ⟨.mkPi h.conj hσ, h.equiv_singleton.symm⟩

/-- For `n ≥ 1` and `m ≤ n`, `𝗜𝚺 n` is axiomatized by `𝗜𝚺 m` together with a single
$\Pi_{n + 2}$ sentence.
- [HP98, Corollary I.4.34(1)]
- [HP98, Remark I.4.35(1)] -/
theorem exists_pi_axiomatization_insert (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hmn : m ≤ n) :
    ∃ π : 𝚷ᴬ_[n + 2].Sentence, 𝗜𝚺 n ≊ insert π.val (𝗜𝚺 m) := by
  obtain ⟨π, hπ⟩ := exists_pi_axiomatization n hn
  refine ⟨π, Equiv.antisymm_iff.mpr ⟨?_, ?_⟩⟩
  · exact hπ.symm.le.trans <| WeakerThan.ofSubset <|
      Set.singleton_subset_iff.mpr <| Set.mem_insert _ _
  · apply WeakerThan.ofAxm!
    rintro φ (rfl | hφ)
    · exact hπ.le.pbl <| by_axm rfl
    · exact (ISigma_weakerThan_of_le hmn).pbl <| by_axm hφ

end ISigma

end FFL.FirstOrder.Arithmetic
