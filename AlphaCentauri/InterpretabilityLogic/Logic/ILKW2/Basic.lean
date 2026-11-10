module

public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic
public import AlphaCentauri.InterpretabilityLogic.Veltman.FrameConditions

/-!
# The logic $\mathbf{ILKW2}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{KW2}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis97] -/
abbrev Logic.ILKW2 : Logic α := Logic.ofAxioms {Axioms.KW2 A B | (A) (B)}

notation "𝐈𝐋𝐊𝐖𝟐" => Logic.ILKW2

namespace Veltman.Model

variable {κ α : Type*} [Nonempty κ] (M : Model κ α)

class IsILKW2 : Prop extends M.IsIL, M.HasW

instance (v : α → Prop) : (pointModel v).IsILKW2 := {}

end Veltman.Model

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILKW2.axiomKW2 : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.KW2 A B := axm ⟨A, B, rfl⟩

lemma ILKW2.axiomKW1Zero : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.KW1Zero A B := by
  have h : 𝐈𝐋𝐊𝐖𝟐 ⊢ B ▷ (B ⋏ ∼(B ⋏ A)) 🡒 B ▷ (B ⋏ ∼A) := rhd_mono_right (by cl_prover);
  cl_prover [h, axiomKW2 (A := B ⋏ A) (B := B)];

lemma ILKW2.axiomF : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.F A := by
  have h₁ : 𝐈𝐋𝐊𝐖𝟐 ⊢ A ▷ (A ⋏ ∼A) 🡒 A ▷ ⊥ := rhd_mono_right (by cl_prover);
  have h₂ : 𝐈𝐋𝐊𝐖𝟐 ⊢ A ▷ ⊥ 🡒 □(∼A) := rhd_bot;
  cl_prover [h₁, h₂, axiomKW2 (A := A) (B := A)];

end Logic

end FFL.InterpretabilityLogic

