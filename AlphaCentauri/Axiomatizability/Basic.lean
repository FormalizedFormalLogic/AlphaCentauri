module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# Axiomatizability

`AxiomatizableBy C T U` says that `U` axiomatizes `T` through sentences satisfying `C`, and
`FiniteAxiomatizableBy T U` that a finite `U` axiomatizes `T`; `Axiomatizable` and
`FiniteAxiomatizable` are the statements that such a `U` exists. Both are AlphaCentauri's own:
Foundation states finite axiomatizability over an arbitrary entailment structure, where the
witness stays implicit.

This module also collects the equivalent forms of finite axiomatizability — a finite **subset**,
a finset, a single sentence — `conj`, the conjunction of that finite theory — the
characterization of the negation, and the finite axiomatizability of `𝗣𝗔⁻`.

- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52]
-/

@[expose] public section

namespace AdjunctiveSet

open FFL.FirstOrder

variable {L : Language}

@[simp] lemma finite_iff_set_finite {T : Theory L} : Finite T ↔ T.Finite := Iff.rfl

end AdjunctiveSet

namespace FFL.FirstOrder

open _root_.FFL.Entailment

variable {L : Language} {C D : Sentence L → Prop} {T U V : Theory L}

/-- `T` is axiomatized by `U` through sentences satisfying `C`: every member of `U` satisfies `C`,
and `T` proves exactly the theorems of `U`.
- [HP98, Discussion III.2.28] -/
structure AxiomatizableBy (C : Sentence L → Prop) (T U : Theory L) : Prop where
  forall_mem : ∀ σ ∈ U, C σ
  equiv : T ≊ U

/-- `T` is axiomatized by the sentences satisfying `C`: some theory of such sentences proves
exactly the theorems of `T`. The axioms of `T` itself need not satisfy `C`.
- [HP98, Discussion III.2.28] -/
def Axiomatizable (C : Sentence L → Prop) (T : Theory L) : Prop :=
  ∃ U : Theory L, AxiomatizableBy C T U

/-- `T` is finitely axiomatized by `U`: `U` is finite and proves exactly the theorems of `T`.
- [Lin97, Ch. 4 §1] -/
structure FiniteAxiomatizableBy (T U : Theory L) : Prop where
  finite : U.Finite
  equiv : T ≊ U

/-- `T` is finitely axiomatizable: some finite theory proves exactly the theorems of `T`.
- [Lin97, Ch. 4 §1] -/
def FiniteAxiomatizable (T : Theory L) : Prop := ∃ U : Theory L, FiniteAxiomatizableBy T U

namespace AxiomatizableBy

lemma refl (h : ∀ σ ∈ T, C σ) : AxiomatizableBy C T T := ⟨h, .refl T⟩

lemma of_equiv (h : AxiomatizableBy C T U) (e : T ≊ V) : AxiomatizableBy C V U :=
  ⟨h.forall_mem, e.symm.trans h.equiv⟩

lemma mono (h : AxiomatizableBy C T U) (hCD : ∀ σ, C σ → D σ) : AxiomatizableBy D T U :=
  ⟨fun σ hσ ↦ hCD σ (h.forall_mem σ hσ), h.equiv⟩

lemma axiomatizable (h : AxiomatizableBy C T U) : Axiomatizable C T := ⟨U, h⟩

end AxiomatizableBy

namespace Axiomatizable

lemma of_forall_mem (h : ∀ σ ∈ T, C σ) : Axiomatizable C T := (AxiomatizableBy.refl h).axiomatizable

lemma of_equiv (h : Axiomatizable C T) (e : T ≊ U) : Axiomatizable C U := by
  obtain ⟨V, hV⟩ := h
  exact (hV.of_equiv e).axiomatizable

lemma mono (h : Axiomatizable C T) (hCD : ∀ σ, C σ → D σ) : Axiomatizable D T := by
  obtain ⟨U, hU⟩ := h
  exact (hU.mono hCD).axiomatizable

end Axiomatizable

/-- Every finite theory is finitely axiomatizable.
- [Lin97, Ch. 4 §1] -/
lemma FiniteAxiomatizable.of_finite (h : T.Finite) : FiniteAxiomatizable T := ⟨T, h, .refl T⟩

/-- Finite axiomatizability is invariant under provability equivalence.
- [Lin97, Ch. 4 §1] -/
lemma FiniteAxiomatizable.of_equiv (h : T ≊ U) :
    FiniteAxiomatizable T → FiniteAxiomatizable U :=
  fun ⟨F, hF, hTF⟩ ↦ ⟨F, hF, h.symm.trans hTF⟩

/-- A theory is finitely axiomatizable iff a finite subtheory axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_finite_subset :
    FiniteAxiomatizable T ↔ ∃ F : Theory L, F ⊆ T ∧ F.Finite ∧ T ≊ F := by
  constructor
  -- Syntactic compactness (`Entailment.Compact`), not the completeness theorem, supplies F.
  · rintro ⟨𝓕, h𝓕fin, h𝓕⟩
    have H : ∀ σ : Sentence L, ∃ F : Theory L, F ⊆ T ∧ F.Finite ∧ (σ ∈ 𝓕 → F ⊢ σ) := by
      intro σ
      by_cases hσ : σ ∈ 𝓕
      · obtain ⟨F, hsub, hfin, hprf⟩ :=
          Compact.finite_provable (h𝓕.symm.le.wk (Axiomatized.by_axm hσ))
        exact ⟨F, hsub, by simpa using hfin, fun _ ↦ hprf⟩
      · exact ⟨∅, by simp, by simp, fun h ↦ absurd h hσ⟩
    choose f hsub hfin hprf using H
    have hsub' : (⋃ σ ∈ 𝓕, f σ) ⊆ T := Set.iUnion₂_subset fun σ _ ↦ hsub σ
    refine ⟨⋃ σ ∈ 𝓕, f σ, hsub', h𝓕fin.biUnion fun σ _ ↦ hfin σ, Equiv.antisymm_iff.mpr
      ⟨h𝓕.le.trans (WeakerThan.ofAxm! ?_), Theory.Proof.weakerThan_of_le hsub'⟩⟩
    intro σ hσ
    replace hσ : σ ∈ 𝓕 := by simpa using hσ
    exact Axiomatized.weakening (Set.subset_biUnion_of_mem hσ) (hprf σ hσ)
  · rintro ⟨F, _, hfin, heq⟩
    exact ⟨F, hfin, heq⟩

/-- A theory is finitely axiomatizable iff a finset of its axioms axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_finset :
    FiniteAxiomatizable T ↔ ∃ F : Finset (Sentence L), ↑F ⊆ T ∧ T ≊ (↑F : Theory L) := by
  constructor
  · intro h
    obtain ⟨F, hsub, hfin, heq⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp h
    exact ⟨hfin.toFinset, by simpa using hsub, by simpa using heq⟩
  · rintro ⟨F, _, heq⟩
    exact ⟨↑F, F.finite_toSet, heq⟩

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

/-- A theory is finitely axiomatizable iff a single sentence axiomatizes it.
- [Lin97, Ch. 4 §1]
- [HP98, Theorem I.2.52] -/
lemma finiteAxiomatizable_iff_exists_sentence :
    FiniteAxiomatizable T ↔ ∃ σ : Sentence L, T ≊ ({σ} : Theory L) := by
  constructor
  · intro h
    obtain ⟨F, _, heq⟩ := finiteAxiomatizable_iff_exists_finset.mp h
    exact ⟨F.conj, heq.trans (equiv_singleton_Fconj F).symm⟩
  · rintro ⟨σ, heq⟩
    exact ⟨{σ}, by simp, heq⟩

lemma FiniteAxiomatizableBy.finiteAxiomatizable (h : FiniteAxiomatizableBy T U) :
    FiniteAxiomatizable T := ⟨U, h⟩

/-- The single sentence that axiomatizes `T`: the conjunction of the finite theory `U`.
- [Lin97, Ch. 4 §1] -/
noncomputable def FiniteAxiomatizableBy.conj (h : FiniteAxiomatizableBy T U) : Sentence L :=
  h.finite.toFinset.conj

lemma FiniteAxiomatizableBy.equiv_singleton (h : FiniteAxiomatizableBy T U) :
    T ≊ ({h.conj} : Theory L) :=
  h.equiv.trans <| by
    have e : (↑h.finite.toFinset : Theory L) = U := by simp
    exact (e ▸ equiv_singleton_Fconj h.finite.toFinset).symm

/-- The single sentence that axiomatizes a finitely axiomatizable theory.
- [Lin97, Ch. 4 §1] -/
noncomputable def FiniteAxiomatizable.conj (h : FiniteAxiomatizable T) : Sentence L :=
  h.choose_spec.conj

lemma FiniteAxiomatizable.equiv_singleton (h : FiniteAxiomatizable T) :
    T ≊ ({h.conj} : Theory L) := h.choose_spec.equiv_singleton

lemma FiniteAxiomatizable.provable_conj (h : FiniteAxiomatizable T) : T ⊢ h.conj :=
  h.equiv_singleton.symm.le.wk (Axiomatized.by_axm rfl)

lemma FiniteAxiomatizable.provable_singleton_iff (h : FiniteAxiomatizable T) {σ : Sentence L} :
    ({h.conj} : Theory L) ⊢ σ ↔ T ⊢ σ := (Equiv.iff.mp h.equiv_singleton σ).symm

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
    exact ⟨hle, fun hle' ↦ h ⟨F, hsub, hfin, Equiv.antisymm_iff.mpr ⟨hle', hle⟩⟩⟩
  · rintro h ⟨F, hsub, hfin, heq⟩
    exact (h F hsub hfin).notWT (Equiv.antisymm_iff.mp heq).1

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic

/-- `𝗣𝗔⁻` is finitely axiomatizable.
- [Lin97, Ch. 4 §1] -/
lemma PeanoMinus.finiteAxiomatizable : FiniteAxiomatizable 𝗣𝗔⁻ :=
  FiniteAxiomatizable.of_finite PeanoMinus.finite

end FFL.FirstOrder.Arithmetic
