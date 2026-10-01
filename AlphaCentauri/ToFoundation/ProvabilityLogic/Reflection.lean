module

public import Foundation.FirstOrder.Incompleteness.Reflection.Local

/-!
# Full local reflection over a finite extension

A consistent extension of `T` by a single sentence never proves the full local reflection schema
of `T`.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- A consistent extension of `T` by a single sentence does not prove the full local reflection
schema of `T`.
- [AB05, Theorem 23] -/
theorem not_provable_localReflectionOn_univ_insert {π : ArithmeticSentence}
    (hC : Consistent (insert π T)) :
    ¬ insert π T ⊢* 𝗥𝗳𝗻[Set.univ] T := fun h ↦
  (T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
    (Γ := fun _ ↦ True) (fun _ _ ↦ trivial) trivial h).not_con hC

end FFL.ProvabilityLogic
