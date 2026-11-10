module

public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# The logics $\mathbf{ILF}$, $\mathbf{ILKW1}^0$ and $\mathbf{ILKW2}$

The extensions of $\mathbf{IL}$ by the principles $\mathsf{F}$, $\mathsf{KW1}^0$ and
$\mathsf{KW2}$, and the equivalence of the last two.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Sve91] -/
abbrev Logic.ILF : Logic α := Logic.ofAxioms {Axioms.F A | (A)}

notation "𝐈𝐋𝐅" => Logic.ILF

/-- - [Sve91] -/
abbrev Logic.ILKW1Zero : Logic α := Logic.ofAxioms {Axioms.KW1Zero A B | (A) (B)}

notation "𝐈𝐋𝐊𝐖𝟏⁰" => Logic.ILKW1Zero

/-- - [Vis97] -/
abbrev Logic.ILKW2 : Logic α := Logic.ofAxioms {Axioms.KW2 A B | (A) (B)}

notation "𝐈𝐋𝐊𝐖𝟐" => Logic.ILKW2

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILF.axiomF : 𝐈𝐋𝐅 ⊢ Axioms.F A := axm ⟨A, rfl⟩

@[simp] lemma ILKW1Zero.axiomKW1Zero : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ Axioms.KW1Zero A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILKW2.axiomKW2 : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.KW2 A B := axm ⟨A, B, rfl⟩

lemma ILKW1Zero.axiomKW2 : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ Axioms.KW2 A B := by
  have h : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ A ▷ ◇B 🡒 (B ⋏ A) ▷ ◇B := rhd_anti_left and₂;
  cl_prover [h, axiomKW1Zero (A := A) (B := B)];

lemma ILKW2.axiomKW1Zero : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.KW1Zero A B := by
  have h : 𝐈𝐋𝐊𝐖𝟐 ⊢ B ▷ (B ⋏ ∼(B ⋏ A)) 🡒 B ▷ (B ⋏ ∼A) := rhd_mono_right (by cl_prover);
  cl_prover [h, axiomKW2 (A := B ⋏ A) (B := B)];

lemma ILKW2.axiomF : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.F A := by
  have h₁ : 𝐈𝐋𝐊𝐖𝟐 ⊢ A ▷ (A ⋏ ∼A) 🡒 A ▷ ⊥ := rhd_mono_right (by cl_prover);
  have h₂ : 𝐈𝐋𝐊𝐖𝟐 ⊢ A ▷ ⊥ 🡒 □(∼A) := rhd_bot;
  cl_prover [h₁, h₂, axiomKW2 (A := A) (B := A)];

instance : (𝐈𝐋𝐅 : Logic α) ⪯ 𝐈𝐋𝐊𝐖𝟐 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, rfl⟩; exact ILKW2.axiomF

instance : (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) ≊ 𝐈𝐋𝐊𝐖𝟐 := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILKW2.axiomKW1Zero)
  (subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILKW1Zero.axiomKW2)

end Logic

end FFL.InterpretabilityLogic

end
