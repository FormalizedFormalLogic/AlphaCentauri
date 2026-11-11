module

public import AlphaCentauri.InterpretabilityLogic.Logic.CLM.Basic

/-!
# The logic $\mathbf{SbCLM}$

The extension of $\mathbf{CL}$ by the principles $\mathsf{M}$ and $\mathsf{Sb}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Ign91, Definition A.1] -/
abbrev Logic.SbCLM : Logic α :=
  Logic.ofCLAxioms ({Axioms.M A B C | (A) (B) (C)} ∪ {Axioms.Sb A B C D | (A) (B) (C) (D)})

notation "𝐒𝐛𝐂𝐋𝐌" => Logic.SbCLM

namespace Logic

open ofCLAxioms

variable {A B C D : Formula α}

@[simp] lemma SbCLM.axiomM : 𝐒𝐛𝐂𝐋𝐌 ⊢ Axioms.M A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma SbCLM.axiomSb : 𝐒𝐛𝐂𝐋𝐌 ⊢ Axioms.Sb A B C D := axm <| .inr ⟨A, B, C, D, rfl⟩

instance : (𝐂𝐋𝐌 : Logic α) ⪯ 𝐒𝐛𝐂𝐋𝐌 := weakerThan_iff.mpr <| subset_of_subset Set.subset_union_left

end Logic

end FFL.InterpretabilityLogic
