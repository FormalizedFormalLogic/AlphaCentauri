module

public import AlphaCentauri.InterpretabilityLogic.Logic.SbCLM.Basic

/-!
# The logic $\mathbf{SCL}$

The extension of $\mathbf{CL}$ by the principles $\mathsf{Sa}$ and $\mathsf{Sb}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Ign91, Definition 2.4] -/
abbrev Logic.SCL : Logic α :=
  Logic.ofCLAxioms ({Axioms.Sa A B C D | (A) (B) (C) (D)} ∪ {Axioms.Sb A B C D | (A) (B) (C) (D)})

notation "𝐒𝐂𝐋" => Logic.SCL

namespace Logic

open ofCLAxioms

variable {A B C D : Formula α}

@[simp] lemma SCL.axiomSa : 𝐒𝐂𝐋 ⊢ Axioms.Sa A B C D := axm <| .inl ⟨A, B, C, D, rfl⟩

@[simp] lemma SCL.axiomSb : 𝐒𝐂𝐋 ⊢ Axioms.Sb A B C D := axm <| .inr ⟨A, B, C, D, rfl⟩

/-- - [Ign91, Proposition 2.5] -/
lemma SCL.axiomM : 𝐒𝐂𝐋 ⊢ Axioms.M A B C := by
  have h₁ : 𝐒𝐂𝐋 ⊢ Axioms.Sa A B (∼C) ⊥ := axiomSa;
  have h₂ : 𝐒𝐂𝐋 ⊢ Axioms.J6 C := axiomJ6;
  have h₃ : 𝐒𝐂𝐋 ⊢ (A ⋏ (∼C ▷ ⊥)) ▷ (B ⋏ (∼C ▷ ⊥)) 🡒 (A ⋏ □C) ▷ (B ⋏ (∼C ▷ ⊥)) :=
    rhd_anti_left (by cl_prover [h₂]);
  have h₄ : 𝐒𝐂𝐋 ⊢ (A ⋏ □C) ▷ (B ⋏ (∼C ▷ ⊥)) 🡒 (A ⋏ □C) ▷ (B ⋏ □C) :=
    rhd_mono_right (by cl_prover [h₂]);
  cl_prover [h₁, h₃, h₄];

/-- - [Ign91, Proposition 2.5] -/
instance : (𝐂𝐋𝐌 : Logic α) ⪯ 𝐒𝐂𝐋 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ ⟨A, B, C, rfl⟩;
  exact SCL.axiomM;

instance : (𝐒𝐛𝐂𝐋𝐌 : Logic α) ⪯ 𝐒𝐂𝐋 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, C, D, rfl⟩);
  · exact SCL.axiomM;
  · exact SCL.axiomSb;

end Logic

end FFL.InterpretabilityLogic
