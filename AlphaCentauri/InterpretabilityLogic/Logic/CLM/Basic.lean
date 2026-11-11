module

public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic

/-!
# The logic $\mathbf{CLM}$

The extension of $\mathbf{CL}$ by the principle $\mathsf{M}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Ign91, Definition 2.3] -/
abbrev Logic.CLM : Logic α := Logic.ofCLAxioms {Axioms.M A B C | (A) (B) (C)}

notation "𝐂𝐋𝐌" => Logic.CLM

namespace Logic

open ofCLAxioms

variable {A B C : Formula α}

@[simp] lemma CLM.axiomM : 𝐂𝐋𝐌 ⊢ Axioms.M A B C := axm ⟨A, B, C, rfl⟩

instance : (𝐂𝐋 : Logic α) ⪯ 𝐂𝐋𝐌 := weakerThan_iff.mpr <| subset_of_subset (Set.empty_subset _)

instance : (𝐂𝐋𝐌 : Logic α) ⪯ 𝐈𝐋𝐌 := by
  rw [weakerThan_iff, ILM, ofILAxioms.eq_ofCLAxioms];
  exact subset_of_subset Set.subset_union_right;

end Logic

end FFL.InterpretabilityLogic
