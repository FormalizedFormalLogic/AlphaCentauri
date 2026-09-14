module

public import Foundation.FirstOrder.Basic

/-!
# Axiomatizability by a class of sentences

`FFL.Entailment.AxiomatizableBy C U T` says that `U` axiomatizes `T` by sentences satisfying `C`,
and `FFL.Entailment.Axiomatizable C T` that some theory does, the analogue for a class of
sentences of Foundation's `Entailment.FiniteAxiomatizable`.
-/

@[expose] public section

namespace FFL.Entailment

open FirstOrder

variable {L : Language} {C D : Sentence L → Prop} {T U V : Theory L}

/-- `U` axiomatizes `T` by sentences satisfying `C`: every member of `U` satisfies `C`, and `U`
proves exactly the theorems of `T`.
- [HP98, Discussion III.2.28] -/
structure AxiomatizableBy (C : Sentence L → Prop) (U T : Theory L) : Prop where
  forall_mem : ∀ σ ∈ U, C σ
  equiv : U ≊ T

/-- `T` is axiomatized by the sentences satisfying `C`: some theory of such sentences proves
exactly the theorems of `T`. The axioms of `T` itself need not satisfy `C`.
- [HP98, Discussion III.2.28] -/
def Axiomatizable (C : Sentence L → Prop) (T : Theory L) : Prop :=
  ∃ U : Theory L, Nonempty (AxiomatizableBy C U T)

namespace AxiomatizableBy

lemma refl (h : ∀ σ ∈ T, C σ) : AxiomatizableBy C T T := ⟨h, Equiv.refl T⟩

lemma trans (h : AxiomatizableBy C U T) (e : T ≊ V) : AxiomatizableBy C U V :=
  ⟨h.forall_mem, h.equiv.trans e⟩

lemma mono (h : AxiomatizableBy C U T) (hCD : ∀ σ, C σ → D σ) : AxiomatizableBy D U T :=
  ⟨fun σ hσ ↦ hCD σ (h.forall_mem σ hσ), h.equiv⟩

lemma axiomatizable (h : AxiomatizableBy C U T) : Axiomatizable C T := ⟨U, ⟨h⟩⟩

end AxiomatizableBy

namespace Axiomatizable

lemma of_forall_mem (h : ∀ σ ∈ T, C σ) : Axiomatizable C T := (AxiomatizableBy.refl h).axiomatizable

lemma of_equiv (h : Axiomatizable C T) (e : T ≊ U) : Axiomatizable C U := by
  obtain ⟨V, ⟨hV⟩⟩ := h
  exact (hV.trans e).axiomatizable

lemma mono (h : Axiomatizable C T) (hCD : ∀ σ, C σ → D σ) : Axiomatizable D T := by
  obtain ⟨U, ⟨hU⟩⟩ := h
  exact (hU.mono hCD).axiomatizable

end Axiomatizable

end FFL.Entailment
