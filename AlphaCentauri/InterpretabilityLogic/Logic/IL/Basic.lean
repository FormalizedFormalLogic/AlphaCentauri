module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic

/-!
# Interpretability logic $\mathbf{IL}$

$\mathbf{IL}$ is the logic `ofAxioms ∅`, contained in every extension by axioms.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis90, §6.1] -/
abbrev Logic.IL : Logic α := Logic.ofAxioms ∅

notation "𝐈𝐋" => Logic.IL

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)}

lemma IL_subset : (𝐈𝐋 : Logic α) ⊆ ofAxioms 𝔸 := subset_of_subset (Set.empty_subset _)

end Logic.ofAxioms

namespace Logic

open ofAxioms

variable {A B C : Formula α}

instance {𝔸 : Set (Formula α)} : (𝐈𝐋 : Logic α) ⪯ ofAxioms 𝔸 := weakerThan_iff.mpr IL_subset

end Logic

end FFL.InterpretabilityLogic

end
