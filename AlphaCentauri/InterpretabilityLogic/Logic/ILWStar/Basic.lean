module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILW.Basic

/-!
# The logics $\mathbf{ILW}^*$ and $\mathbf{ILM}_0\mathbf{W}$

The extensions of $\mathbf{IL}$ by the principle $\mathsf{W}^*$, and by $\mathsf{M}_0$ and
$\mathsf{W}$, which coincide.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Vis97] -/
abbrev Logic.ILWStar : Logic α := Logic.ofAxioms {Axioms.Wstar A B C | (A) (B) (C)}

notation "𝐈𝐋𝐖*" => Logic.ILWStar

abbrev Logic.ILM₀W : Logic α :=
  Logic.ofAxioms ({Axioms.M₀ A B C | (A) (B) (C)} ∪ {Axioms.W A B | (A) (B)})

notation "𝐈𝐋𝐌₀𝐖" => Logic.ILM₀W

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILWStar.axiomWstar : 𝐈𝐋𝐖* ⊢ Axioms.Wstar A B C := axm ⟨A, B, C, rfl⟩

@[simp] lemma ILM₀W.axiomM₀ : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.M₀ A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma ILM₀W.axiomW : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.W A B := axm <| .inr ⟨A, B, rfl⟩

lemma ILWStar.axiomW : 𝐈𝐋𝐖* ⊢ Axioms.W A B := by
  have h₁ : (𝐈𝐋𝐖* : Logic α) ⊢ □⊤ := nec verum;
  have h₂ : 𝐈𝐋𝐖* ⊢ A ▷ B 🡒 A ▷ (B ⋏ □⊤) := rhd_mono_right (by cl_prover [h₁]);
  have h₃ : 𝐈𝐋𝐖* ⊢ (B ⋏ □⊤) ▷ (B ⋏ □⊤ ⋏ □(∼A)) 🡒 (B ⋏ □⊤) ▷ (B ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  have h₄ : 𝐈𝐋𝐖* ⊢ Axioms.J2 A (B ⋏ □⊤) (B ⋏ □(∼A)) := axiomJ2;
  cl_prover [axiomWstar (A := A) (B := B) (C := ⊤), h₂, h₃, h₄];

lemma ILWStar.axiomM₀ : 𝐈𝐋𝐖* ⊢ Axioms.M₀ A B C := by
  have h₁ : 𝐈𝐋𝐖* ⊢ A ▷ B 🡒 A ▷ (B ⋎ ◇A) := rhd_mono_right or₁;
  have h₂ : 𝐈𝐋𝐖* ⊢ (B ⋎ ∼□(∼A)) ⋏ □C ⋏ □(∼A) 🡒 B ⋏ □C := by cl_prover;
  have h₃ : 𝐈𝐋𝐖* ⊢ ((B ⋎ ◇A) ⋏ □C) ▷ ((B ⋎ ◇A) ⋏ □C ⋏ □(∼A)) 🡒 ((B ⋎ ◇A) ⋏ □C) ▷ (B ⋏ □C) :=
    rhd_mono_right h₂;
  have h₄ : 𝐈𝐋𝐖* ⊢ ((B ⋎ ◇A) ⋏ □C) ▷ (B ⋏ □C) 🡒 (◇A ⋏ □C) ▷ (B ⋏ □C) :=
    rhd_anti_left (by cl_prover);
  cl_prover [axiomWstar (A := A) (B := B ⋎ ◇A) (C := C), h₁, h₃, h₄];

lemma ILM₀W.axiomWstar : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.Wstar A B C := by
  have h₁ : 𝐈𝐋𝐌₀𝐖 ⊢ B ⋏ □C 🡒 B ⋏ □C ⋏ ∼□(∼A) ⋎ B ⋏ □C ⋏ □(∼A) := by cl_prover;
  have h₂ : 𝐈𝐋𝐌₀𝐖 ⊢ (B ⋏ □C) ▷ (B ⋏ □C ⋏ ◇A ⋎ B ⋏ □C ⋏ □(∼A)) := rhd_of_provable h₁;
  have h₃ : 𝐈𝐋𝐌₀𝐖 ⊢ (◇A ⋏ □C) ▷ ((B ⋏ □(∼A)) ⋏ □C) 🡒 (B ⋏ □C ⋏ ◇A) ▷ ((B ⋏ □(∼A)) ⋏ □C) :=
    rhd_anti_left (by cl_prover);
  have h₄ : 𝐈𝐋𝐌₀𝐖 ⊢
      (B ⋏ □C ⋏ ◇A) ▷ ((B ⋏ □(∼A)) ⋏ □C) 🡒 (B ⋏ □C ⋏ ◇A) ▷ (B ⋏ □C ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  have h₅ : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.J3 (B ⋏ □C ⋏ ◇A) (B ⋏ □C ⋏ □(∼A)) (B ⋏ □C ⋏ □(∼A)) := axiomJ3;
  have h₆ : 𝐈𝐋𝐌₀𝐖 ⊢
      Axioms.J2 (B ⋏ □C) (B ⋏ □C ⋏ ◇A ⋎ B ⋏ □C ⋏ □(∼A)) (B ⋏ □C ⋏ □(∼A)) := axiomJ2;
  have h₇ : 𝐈𝐋𝐌₀𝐖 ⊢ (B ⋏ □C ⋏ □(∼A)) ▷ (B ⋏ □C ⋏ □(∼A)) := rhd_refl;
  cl_prover [axiomW (A := A) (B := B), axiomM₀ (A := A) (B := B ⋏ □(∼A)) (C := C), h₂, h₃, h₄,
    h₅, h₆, h₇];

instance : (𝐈𝐋𝐖 : Logic α) ⪯ 𝐈𝐋𝐖* :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILWStar.axiomW

instance : (𝐈𝐋𝐖* : Logic α) ≊ 𝐈𝐋𝐌₀𝐖 := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILM₀W.axiomWstar)
  (subset_of_provable <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
    · exact ILWStar.axiomM₀
    · exact ILWStar.axiomW)

instance : (𝐈𝐋𝐌₀ : Logic α) ⪯ 𝐈𝐋𝐌₀𝐖 := weakerThan_iff.mpr <| subset_of_subset Set.subset_union_left

end Logic

end FFL.InterpretabilityLogic

end
