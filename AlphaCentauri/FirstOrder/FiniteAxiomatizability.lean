module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# Finite axiomatizability

Finite axiomatizability for first-order theories:

* the finite **subset** form `finiteAxiomatizable_iff_exists_finite_subset`;
* the finset form `finiteAxiomatizable_iff_exists_finset` and the single-sentence form
  `finiteAxiomatizable_iff_exists_sentence`, through `equiv_singleton_Fconj`
  (with private list-based counterparts `finiteAxiomatizable_iff_exists_list` and
  `equiv_singleton_Conj₂`);
* the characterization `not_finiteAxiomatizable_iff` of the negation;
* invariance under provability equivalence, `Entailment.FiniteAxiomatizable.of_equiv`;
* finite axiomatizability of `𝗣𝗔⁻`.
-/

@[expose] public section

namespace AdjunctiveSet

open FFL.FirstOrder

variable {L : Language}

@[simp] lemma finite_iff_set_finite {T : Theory L} : Finite T ↔ T.Finite := Iff.rfl

end AdjunctiveSet

namespace FFL.Entailment

open FirstOrder

variable {L : Language} {T : Theory L}

/-- Every finite theory is finitely axiomatizable.
- [Lin97, Ch. 4 §1] -/
lemma FiniteAxiomatizable.of_finite (h : T.Finite) : FiniteAxiomatizable T :=
  ⟨T, by simpa using h, Equiv.refl T⟩

/-- Finite axiomatizability is invariant under provability equivalence.
- [Lin97, Ch. 4 §1] -/
lemma FiniteAxiomatizable.of_equiv {U : Theory L} (h : T ≊ U) :
    FiniteAxiomatizable T → FiniteAxiomatizable U :=
  fun ⟨F, hF, hFT⟩ ↦ ⟨F, hF, hFT.trans h⟩

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

/-- A theory is finitely axiomatizable iff a finset of its axioms axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_finset :
    FiniteAxiomatizable T ↔ ∃ F : Finset (Sentence L), ↑F ⊆ T ∧ (↑F : Theory L) ≊ T := by
  constructor
  · intro h
    obtain ⟨F, hsub, hfin, heq⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp h
    exact ⟨hfin.toFinset, by simpa using hsub, by simpa using heq⟩
  · rintro ⟨F, _, heq⟩
    exact ⟨↑F, F.finite_toSet, heq⟩

/-- A theory is finitely axiomatizable iff a list of its axioms axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
private lemma finiteAxiomatizable_iff_exists_list :
    FiniteAxiomatizable T ↔
      ∃ l : List (Sentence L), (∀ σ ∈ l, σ ∈ T) ∧ ({σ | σ ∈ l} : Theory L) ≊ T := by
  constructor
  · intro h
    obtain ⟨F, hsub, hfin, heq⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp h
    have hl : ({σ | σ ∈ hfin.toFinset.toList} : Theory L) = F := by ext σ; simp
    exact ⟨hfin.toFinset.toList, fun σ hσ ↦ hsub (by simpa using hσ), hl.symm ▸ heq⟩
  · rintro ⟨l, _, heq⟩
    exact ⟨{σ | σ ∈ l}, by simp, heq⟩

/-- The conjunction of a finset of sentences axiomatizes the theory of its members.
- [Lin97, Ch. 4 §1] -/
lemma equiv_singleton_Fconj (F : Finset (Sentence L)) :
    ({F.conj} : Theory L) ≊ (↑F : Theory L) := by
  classical
  refine Equiv.antisymm_iff.mpr ⟨WeakerThan.ofAxm! ?_, WeakerThan.ofAxm! ?_⟩
  · rintro σ (rfl : σ = F.conj)
    exact FConj_iff_forall_provable.mpr fun φ hφ ↦ Axiomatized.by_axm hφ
  · intro σ hσ
    exact mdp (left_Fconj_intro (show σ ∈ F by simpa using hσ)) (Axiomatized.by_axm rfl)

/-- The conjunction of a list of sentences axiomatizes the theory of its members.
- [Lin97, Ch. 4 §1] -/
private lemma equiv_singleton_Conj₂ (l : List (Sentence L)) :
    ({⋀l} : Theory L) ≊ ({σ | σ ∈ l} : Theory L) := by
  classical
  refine Equiv.antisymm_iff.mpr ⟨WeakerThan.ofAxm! ?_, WeakerThan.ofAxm! ?_⟩
  · rintro σ (rfl : σ = ⋀l)
    exact Conj₂_iff_forall_provable.mpr fun φ hφ ↦ Axiomatized.by_axm hφ
  · intro σ hσ
    exact mdp (left_Conj₂_intro (show σ ∈ l by simpa using hσ)) (Axiomatized.by_axm rfl)

/-- A theory is finitely axiomatizable iff a single sentence axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_sentence :
    FiniteAxiomatizable T ↔ ∃ σ : Sentence L, ({σ} : Theory L) ≊ T := by
  constructor
  · intro h
    obtain ⟨F, _, heq⟩ := finiteAxiomatizable_iff_exists_finset.mp h
    exact ⟨F.conj, (equiv_singleton_Fconj F).trans heq⟩
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
    exact ⟨hle, fun hle' ↦ h ⟨F, hsub, hfin, Equiv.antisymm_iff.mpr ⟨hle, hle'⟩⟩⟩
  · rintro h ⟨F, hsub, hfin, heq⟩
    exact (h F hsub hfin).notWT (Equiv.antisymm_iff.mp heq).2

end FFL.Entailment

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment in
/-- `𝗣𝗔⁻` is finitely axiomatizable.
- [Lin97, Ch. 4 §1] -/
lemma PeanoMinus.finiteAxiomatizable : FiniteAxiomatizable 𝗣𝗔⁻ :=
  FiniteAxiomatizable.of_finite PeanoMinus.finite

end FFL.FirstOrder.Arithmetic
