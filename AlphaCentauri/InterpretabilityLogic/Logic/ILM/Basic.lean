module

public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# The logic $\mathbf{ILM}$

The extension of $\mathbf{IL}$ by the principle $\mathsf{M}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis90, §6.4] -/
abbrev Logic.ILM : Logic α := Logic.ofAxioms {Axioms.M A B C | (A) (B) (C)}

notation "𝐈𝐋𝐌" => Logic.ILM

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILM.axiomM : 𝐈𝐋𝐌 ⊢ Axioms.M A B C := axm ⟨A, B, C, rfl⟩

/-- - [Vis90, §6.4.1] -/
lemma ILM.axiomW : 𝐈𝐋𝐌 ⊢ Axioms.W A B := by
  have h₁ : 𝐈𝐋𝐌 ⊢ A ▷ (A ⋏ □(∼A)) := rhd_and_box_neg;
  have h₂ : 𝐈𝐋𝐌 ⊢ Axioms.M A B (∼A) := axiomM;
  have h₃ : 𝐈𝐋𝐌 ⊢ Axioms.J2 A (A ⋏ □(∼A)) (B ⋏ □(∼A)) := axiomJ2;
  cl_prover [h₁, h₂, h₃];

lemma ILM.axiomR : 𝐈𝐋𝐌 ⊢ Axioms.R A B C := by
  have h₁ : 𝐈𝐋𝐌 ⊢ A ▷ A ⋏ ∼(A ▷ ∼C) 🡒 ◇(A ⋏ □C) := rhd_and_not_rhd_neg;
  have h₂ : 𝐈𝐋𝐌 ⊢ A ▷ A := rhd_refl;
  have h₃ : 𝐈𝐋𝐌 ⊢ ∼(A ▷ ∼C) 🡒 ◇(A ⋏ □C) := by cl_prover [h₁, h₂];
  have h₄ : 𝐈𝐋𝐌 ⊢ ◇(A ⋏ □C) ▷ (A ⋏ □C) := axiomJ5;
  have h₅ : 𝐈𝐋𝐌 ⊢ Axioms.J2 (∼(A ▷ ∼C)) (◇(A ⋏ □C)) (A ⋏ □C) := axiomJ2;
  have h₆ : 𝐈𝐋𝐌 ⊢ Axioms.J2 (∼(A ▷ ∼C)) (A ⋏ □C) (B ⋏ □C) := axiomJ2;
  cl_prover [rhd_of_provable h₃, h₄, h₅, h₆, axiomM (A := A) (B := B) (C := C)];

end Logic

end FFL.InterpretabilityLogic

end
