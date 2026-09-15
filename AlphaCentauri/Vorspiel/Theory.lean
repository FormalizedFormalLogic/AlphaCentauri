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

variable {L : Language} {T U : Theory L}

lemma WeakerThan.union_right (h : T ⪯ U) (S : Theory L) : S ∪ T ⪯ S ∪ U :=
  WeakerThan.ofAxm! $ by
    rintro φ (hφ | hφ)
    · exact by_axm (Set.mem_union_left _ hφ)
    · exact WeakerThan.pbl (h.pbl (by_axm hφ))

lemma Equiv.union_right (e : T ≊ U) (S : Theory L) : S ∪ T ≊ S ∪ U :=
  Equiv.antisymm ⟨e.le.union_right S, e.symm.le.union_right S⟩

end FFL.Entailment
