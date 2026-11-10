module

public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# The logic $\mathbf{ILM}_0$

The extension of $\mathbf{IL}$ by the principle $\mathsf{M}_0$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis97] -/
abbrev Logic.ILM₀ : Logic α := Logic.ofAxioms {Axioms.M₀ A B C | (A) (B) (C)}

notation "𝐈𝐋𝐌₀" => Logic.ILM₀

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILM₀.axiomM₀ : 𝐈𝐋𝐌₀ ⊢ Axioms.M₀ A B C := axm ⟨A, B, C, rfl⟩

end Logic

end FFL.InterpretabilityLogic

end
