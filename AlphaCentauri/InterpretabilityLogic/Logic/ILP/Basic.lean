module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILR.Basic

/-!
# The logic $\mathbf{ILP}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{P}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis90, §6.3] -/
abbrev Logic.ILP : Logic α := Logic.ofAxioms {Axioms.P A B | (A) (B)}

notation "𝐈𝐋𝐏" => Logic.ILP

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILP.axiomP : 𝐈𝐋𝐏 ⊢ Axioms.P A B := axm ⟨A, B, rfl⟩

/-- - [Vis90, §6.3] -/
lemma ILP.axiomW : 𝐈𝐋𝐏 ⊢ Axioms.W A B := by
  have h₁ : 𝐈𝐋𝐏 ⊢ □(A ▷ B) 🡒 □(◇A 🡒 ◇B) := box_mono axiomJ4;
  have h₂ : 𝐈𝐋𝐏 ⊢ (∼□(∼A) 🡒 ∼□(∼B)) 🡒 B ⋏ □(∼B) 🡒 B ⋏ □(∼A) := by cl_prover;
  have h₃ : 𝐈𝐋𝐏 ⊢ □(◇A 🡒 ◇B) 🡒 □(B ⋏ □(∼B) 🡒 B ⋏ □(∼A)) := box_mono h₂;
  have h₄ : 𝐈𝐋𝐏 ⊢ Axioms.J1 (B ⋏ □(∼B)) (B ⋏ □(∼A)) := axiomJ1;
  have h₅ : 𝐈𝐋𝐏 ⊢ B ▷ (B ⋏ □(∼B)) := rhd_and_box_neg;
  have h₆ : 𝐈𝐋𝐏 ⊢ Axioms.J2 B (B ⋏ □(∼B)) (B ⋏ □(∼A)) := axiomJ2;
  have h₇ : 𝐈𝐋𝐏 ⊢ Axioms.J2 A B (B ⋏ □(∼A)) := axiomJ2;
  cl_prover [axiomP (A := A) (B := B), h₁, h₃, h₄, h₅, h₆, h₇];

lemma ILP.axiomR : 𝐈𝐋𝐏 ⊢ Axioms.R A B C := by
  have h₁ : 𝐈𝐋𝐏 ⊢ A ▷ B 🡒 ∼(A ▷ ∼C) 🡒 A ▷ B ⋏ ∼(A ▷ ∼C) := by cl_prover;
  have h₂ : 𝐈𝐋𝐏 ⊢ Axioms.J1 (∼(A ▷ ∼C)) (A ▷ B ⋏ ∼(A ▷ ∼C)) := axiomJ1;
  have h₃ : 𝐈𝐋𝐏 ⊢ (A ▷ B ⋏ ∼(A ▷ ∼C)) ▷ ◇(B ⋏ □C) := rhd_of_provable rhd_and_not_rhd_neg;
  have h₄ : 𝐈𝐋𝐏 ⊢ ◇(B ⋏ □C) ▷ (B ⋏ □C) := axiomJ5;
  have h₅ : 𝐈𝐋𝐏 ⊢ Axioms.J2 (∼(A ▷ ∼C)) (A ▷ B ⋏ ∼(A ▷ ∼C)) (◇(B ⋏ □C)) := axiomJ2;
  have h₆ : 𝐈𝐋𝐏 ⊢ Axioms.J2 (∼(A ▷ ∼C)) (◇(B ⋏ □C)) (B ⋏ □C) := axiomJ2;
  cl_prover [axiomP (A := A) (B := B), box_mono h₁, h₂, h₃, h₄, h₅, h₆];

instance : (𝐈𝐋𝐑𝐖 : Logic α) ⪯ 𝐈𝐋𝐏 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
  · exact ILP.axiomR
  · exact ILP.axiomW

end Logic

end FFL.InterpretabilityLogic

end
