module

public import Foundation.FirstOrder.Basic.Calculus

/-!
# Unions of theories

Relative strength and provable equivalence of theories are preserved by taking the union with a
fixed theory.
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
