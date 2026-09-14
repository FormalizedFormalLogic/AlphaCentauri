module

public import Foundation.FirstOrder.Basic

/-!
# Axiomatizability by a class of sentences

`FFL.Entailment.Axiomatizable C T` says that `T` is axiomatized by the sentences satisfying `C`,
the analogue for a class of sentences of Foundation's `Entailment.FiniteAxiomatizable`.
-/

@[expose] public section

namespace FFL.Entailment

open FirstOrder

variable {L : Language} {C D : Sentence L → Prop} {T U : Theory L}

/-- `T` is axiomatized by the sentences satisfying `C`: some theory all of whose members satisfy
`C` proves exactly the theorems of `T`. Its own axioms need not satisfy `C`.
- [HP98, Discussion III.2.28] -/
def Axiomatizable (C : Sentence L → Prop) (T : Theory L) : Prop :=
  ∃ U : Theory L, (∀ σ ∈ U, C σ) ∧ U ≊ T

namespace Axiomatizable

lemma of_forall_mem (h : ∀ σ ∈ T, C σ) : Axiomatizable C T := ⟨T, h, Equiv.refl T⟩

lemma of_equiv (h : Axiomatizable C T) (e : T ≊ U) : Axiomatizable C U := by
  obtain ⟨V, hV, hVT⟩ := h
  exact ⟨V, hV, hVT.trans e⟩

lemma mono (h : Axiomatizable C T) (hCD : ∀ σ, C σ → D σ) : Axiomatizable D T := by
  obtain ⟨V, hV, hVT⟩ := h
  exact ⟨V, fun σ hσ ↦ hCD σ (hV σ hσ), hVT⟩

end Axiomatizable

end FFL.Entailment
