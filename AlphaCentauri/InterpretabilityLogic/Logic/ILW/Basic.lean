module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILKW2.Basic

/-!
# The logic $\mathbf{ILW}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{W}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis90, §6.2] -/
abbrev Logic.ILW : Logic α := Logic.ofAxioms {Axioms.W A B | (A) (B)}

notation "𝐈𝐋𝐖" => Logic.ILW

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILW.axiomW : 𝐈𝐋𝐖 ⊢ Axioms.W A B := axm ⟨A, B, rfl⟩

/-- - [Vis90, §6.2.1] -/
lemma ILW.axiomKW2 : 𝐈𝐋𝐖 ⊢ Axioms.KW2 A B := by
  have h₁ : 𝐈𝐋𝐖 ⊢ ∼(B ⋏ ∼A) 🡒 ∼A 🡒 ∼B := by cl_prover;
  have h₂ : 𝐈𝐋𝐖 ⊢ □(∼A 🡒 ∼B) 🡒 □(∼A) 🡒 □(∼B) := axiomK;
  have h₃ : 𝐈𝐋𝐖 ⊢ ∼□(∼B) ⋏ □(∼A) 🡒 ∼□(∼(B ⋏ ∼A)) := by cl_prover [box_mono h₁, h₂];
  have h₄ : 𝐈𝐋𝐖 ⊢ A ▷ (◇B ⋏ □(∼A)) 🡒 A ▷ ◇(B ⋏ ∼A) := rhd_mono_right h₃;
  have h₅ : 𝐈𝐋𝐖 ⊢ ◇(B ⋏ ∼A) ▷ (B ⋏ ∼A) := axiomJ5;
  have h₆ : 𝐈𝐋𝐖 ⊢ Axioms.J2 A (◇(B ⋏ ∼A)) (B ⋏ ∼A) := axiomJ2;
  have h₇ : 𝐈𝐋𝐖 ⊢ Axioms.J3 (B ⋏ ∼A) A (B ⋏ ∼A) := axiomJ3;
  have h₈ : 𝐈𝐋𝐖 ⊢ (B ⋏ ∼A ⋎ A) ▷ (B ⋏ ∼A) 🡒 B ▷ (B ⋏ ∼A) := rhd_anti_left (by cl_prover);
  have h₉ : 𝐈𝐋𝐖 ⊢ (B ⋏ ∼A) ▷ (B ⋏ ∼A) := rhd_refl;
  cl_prover [axiomW (A := A) (B := ◇B), h₄, h₅, h₆, h₇, h₈, h₉];

instance : (𝐈𝐋𝐊𝐖𝟐 : Logic α) ⪯ 𝐈𝐋𝐖 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILW.axiomKW2

end Logic

end FFL.InterpretabilityLogic

end
