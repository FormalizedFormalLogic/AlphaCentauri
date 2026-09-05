module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# Finite axiomatizability

Finite axiomatizability for first-order theories:

* the finite **subset** form `finiteAxiomatizable_iff_exists_finite_subset`;
* the list form `finiteAxiomatizable_iff_exists_list` and the single-sentence form
  `finiteAxiomatizable_iff_exists_sentence`;
* the characterization `not_finiteAxiomatizable_iff` of the negation;
* invariance under provability equivalence, `Entailment.FiniteAxiomatizable.of_equiv`;
* finite axiomatizability of `𝗣𝗔⁻`.
-/

@[expose] public section

namespace AdjunctiveSet

open LO.FirstOrder

variable {L : Language}

@[simp] lemma finite_iff_set_finite {T : Theory L} : Finite T ↔ T.Finite := Iff.rfl

end AdjunctiveSet

namespace LO.Entailment

open FirstOrder

variable {L : Language} {T U : Theory L}

/-- Every finite theory is finitely axiomatizable.
- [Lin97, Ch. 4 §1] -/
lemma FiniteAxiomatizable.of_finite (h : T.Finite) : FiniteAxiomatizable T :=
  ⟨T, by simpa using h, Equiv.refl T⟩

/-- Finite axiomatizability is invariant under provability equivalence.
- [Lin97, Ch. 4 §1] -/
lemma FiniteAxiomatizable.of_equiv (h : T ≊ U) :
    FiniteAxiomatizable T → FiniteAxiomatizable U := by
  rintro ⟨F, hF, hFT⟩
  exact ⟨F, hF, hFT.trans h⟩

/-- A theory is finitely axiomatizable iff a finite subtheory axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_finite_subset :
    FiniteAxiomatizable T ↔ ∃ F : Theory L, F ⊆ T ∧ F.Finite ∧ F ≊ T := by
  constructor
  -- Syntactic compactness (`Entailment.Compact`), not the completeness theorem, supplies F.
  · rintro ⟨𝓕, h𝓕fin, h𝓕⟩
    replace h𝓕fin : (𝓕 : Set (Sentence L)).Finite := by simpa using h𝓕fin
    have H : ∀ σ : Sentence L, ∃ F : Theory L, F ⊆ T ∧ F.Finite ∧ (σ ∈ 𝓕 → F ⊢ σ) := by
      intro σ
      by_cases hσ : σ ∈ 𝓕
      · obtain ⟨F, hsub, hfin, hprf⟩ :=
          Compact.finite_provable (h𝓕.le.wk (Axiomatized.by_axm hσ))
        exact ⟨F, hsub, by simpa using hfin, fun _ ↦ hprf⟩
      · exact ⟨∅, by simp, by simp, fun h ↦ absurd h hσ⟩
    choose f hsub hfin hprf using H
    have hsub' : (⋃ σ ∈ 𝓕, f σ) ⊆ T := Set.iUnion₂_subset fun σ _ ↦ hsub σ
    refine ⟨⋃ σ ∈ 𝓕, f σ, hsub', h𝓕fin.biUnion fun σ _ ↦ hfin σ, Equiv.antisymm_iff.mpr
      ⟨Theory.Proof.weakerThan_of_le hsub', h𝓕.symm.le.trans (WeakerThan.ofAxm! ?_)⟩⟩
    intro σ hσ
    replace hσ : σ ∈ 𝓕 := by simpa using hσ
    exact Axiomatized.weakening! (Set.subset_biUnion_of_mem hσ) (hprf σ hσ)
  · rintro ⟨F, _, hfin, heq⟩
    exact ⟨F, by simpa using hfin, heq⟩

/-- A theory is finitely axiomatizable iff a list of its axioms axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_list :
    FiniteAxiomatizable T ↔
      ∃ l : List (Sentence L), (∀ σ ∈ l, σ ∈ T) ∧ ({σ | σ ∈ l} : Theory L) ≊ T := by
  constructor
  · intro h
    obtain ⟨F, hsub, hfin, heq⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp h
    have hl : ({σ | σ ∈ hfin.toFinset.toList} : Theory L) = F := by ext σ; simp
    exact ⟨hfin.toFinset.toList, fun σ hσ ↦ hsub (by simpa using hσ), by rw [hl]; exact heq⟩
  · rintro ⟨l, _, heq⟩
    exact ⟨{σ | σ ∈ l}, by simp, heq⟩

/-- A theory is finitely axiomatizable iff a single sentence axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_sentence :
    FiniteAxiomatizable T ↔ ∃ σ : Sentence L, ({σ} : Theory L) ≊ T := by
  classical
  constructor
  · intro h
    obtain ⟨l, _, heq⟩ := finiteAxiomatizable_iff_exists_list.mp h
    refine ⟨⋀l, Equiv.trans
      (Equiv.antisymm_iff.mpr ⟨WeakerThan.ofAxm! ?_, WeakerThan.ofAxm! ?_⟩) heq⟩
    · rintro σ (rfl : σ = ⋀l)
      exact Conj₂_iff_forall_provable.mpr fun φ hφ ↦ Axiomatized.by_axm hφ
    · intro σ hσ
      exact mdp (left_Conj₂_intro (show σ ∈ l by simpa using hσ)) (Axiomatized.by_axm rfl)
  · rintro ⟨σ, heq⟩
    exact ⟨{σ}, by simp, heq⟩

/-- A theory fails to be finitely axiomatizable exactly when every finite subtheory of it is
strictly weaker.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma not_finiteAxiomatizable_iff :
    ¬FiniteAxiomatizable T ↔ ∀ F : Theory L, F ⊆ T → F.Finite → F ⪱ T := by
  rw [finiteAxiomatizable_iff_exists_finite_subset]
  constructor
  · intro h F hsub hfin
    have hle : F ⪯ T := Theory.Proof.weakerThan_of_le hsub
    refine ⟨hle, fun hle' ↦ h ⟨F, hsub, hfin, Equiv.antisymm_iff.mpr ⟨hle, hle'⟩⟩⟩
  · rintro h ⟨F, hsub, hfin, heq⟩
    exact (h F hsub hfin).notWT (Equiv.antisymm_iff.mp heq).2

end LO.Entailment

namespace LO.FirstOrder.Arithmetic

/-- `𝗣𝗔⁻` is finitely axiomatizable.
- [Lin97, Ch. 4 §1] -/
lemma PeanoMinus.finiteAxiomatizable :
    Entailment.FiniteAxiomatizable (𝗣𝗔⁻ : ArithmeticTheory) :=
  Entailment.FiniteAxiomatizable.of_finite PeanoMinus.finite

end LO.FirstOrder.Arithmetic
