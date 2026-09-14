module

public import Foundation.FirstOrder.Basic

/-!
# Axiomatizability by a class of sentences

`FFL.Entailment.AxiomatizableBy C T U` says that `T` is axiomatized by `U` through sentences
satisfying `C`, and `FFL.Entailment.Axiomatizable C T` that some theory axiomatizes `T` that way,
the analogue for a class of sentences of Foundation's `Entailment.FiniteAxiomatizable`.
-/

@[expose] public section

namespace FFL.Entailment

open FirstOrder

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
  ∃ U : Theory L, Nonempty (AxiomatizableBy C T U)

namespace AxiomatizableBy

lemma refl (h : ∀ σ ∈ T, C σ) : AxiomatizableBy C T T := ⟨h, Equiv.refl T⟩

lemma of_equiv (h : AxiomatizableBy C T U) (e : T ≊ V) : AxiomatizableBy C V U :=
  ⟨h.forall_mem, e.symm.trans h.equiv⟩

lemma mono (h : AxiomatizableBy C T U) (hCD : ∀ σ, C σ → D σ) : AxiomatizableBy D T U :=
  ⟨fun σ hσ ↦ hCD σ (h.forall_mem σ hσ), h.equiv⟩

lemma axiomatizable (h : AxiomatizableBy C T U) : Axiomatizable C T := ⟨U, ⟨h⟩⟩

end AxiomatizableBy

namespace Axiomatizable

lemma of_forall_mem (h : ∀ σ ∈ T, C σ) : Axiomatizable C T := (AxiomatizableBy.refl h).axiomatizable

lemma of_equiv (h : Axiomatizable C T) (e : T ≊ U) : Axiomatizable C U := by
  obtain ⟨V, ⟨hV⟩⟩ := h
  exact (hV.of_equiv e).axiomatizable

lemma mono (h : Axiomatizable C T) (hCD : ∀ σ, C σ → D σ) : Axiomatizable D T := by
  obtain ⟨U, ⟨hU⟩⟩ := h
  exact (hU.mono hCD).axiomatizable

end Axiomatizable

end FFL.Entailment
