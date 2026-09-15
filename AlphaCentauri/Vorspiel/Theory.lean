module

public import Foundation.FirstOrder.Basic.Calculus
public import Foundation.Meta.ClProver

/-!
# Theories, unions and adjoined sentences

Gaps in Foundation about theories as sets of sentences: union with a fixed theory preserves
relative strength and provable equivalence, refutation transfers along a provable equivalence, and
adjoining a sentence is inconsistent exactly when the theory refutes it.
-/

@[expose] public section

namespace FFL.Entailment

open FFL.FirstOrder

variable {L : Language} {U S : Theory L}

lemma WeakerThan.union_right (h : U ⪯ S) (T : Theory L) : T ∪ U ⪯ T ∪ S :=
  WeakerThan.ofAxm! $ by
    rintro φ (hφ | hφ)
    · exact by_axm (Set.mem_union_left _ hφ)
    · exact WeakerThan.pbl (h.pbl (by_axm hφ))

lemma Equiv.union_right (e : U ≊ S) (T : Theory L) : T ∪ U ≊ T ∪ S :=
  Equiv.antisymm ⟨e.le.union_right T, e.symm.le.union_right T⟩

end FFL.Entailment

namespace FFL.FirstOrder

open FFL.Entailment

variable {L : Language} {T : Theory L} {φ ψ : Sentence L} [L.DecidableEq]

lemma provable_neg_iff (e : T ⊢ φ 🡘 ψ) : T ⊢ ∼φ ↔ T ⊢ ∼ψ :=
  ⟨fun h ↦ by cl_prover [e, h], fun h ↦ by cl_prover [e, h]⟩

private lemma inconsistent_insert_iff : Inconsistent (insert φ T) ↔ T ⊢ ∼φ := by
  show Inconsistent (adjoin φ T) ↔ T ⊢ ∼φ
  simpa using (provable_iff_inconsistent_adjoin (𝓢 := T) (φ := ∼φ)).symm

lemma provable_neg_of_inconsistent_insert (h : Inconsistent (insert φ T)) : T ⊢ ∼φ :=
  inconsistent_insert_iff.mp h

lemma inconsistent_insert_of_provable_neg (h : T ⊢ ∼φ) : Inconsistent (insert φ T) :=
  inconsistent_insert_iff.mpr h

end FFL.FirstOrder
