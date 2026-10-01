module

public import Foundation.Logic.Entailment

/-!
# Consistency as a simp lemma

`simp` cannot close a goal `Consistent 𝓢` on its own, even when an instance is available; this
records `Consistent 𝓢` as a simp lemma whenever such an instance can be synthesized.
-/

@[expose] public section

namespace FFL.Entailment

variable {F : Type*} {S : Type*} [Entailment S F]

@[simp] lemma consistent_eq_true (𝓢 : S) [h : Consistent 𝓢] : Consistent 𝓢 = True :=
  eq_true h

end FFL.Entailment
