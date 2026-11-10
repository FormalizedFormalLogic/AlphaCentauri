module

public import AlphaCentauri.InterpretabilityLogic.Logic.ILMZero.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILWStar.Basic

/-!
# The logics $\mathbf{ILP}_0$, $\mathbf{ILR}$, $\mathbf{ILRW}$ and $\mathbf{ILR}^*$

The extensions of $\mathbf{IL}$ by the principles $\mathsf{P}_0$, $\mathsf{R}$, $\mathsf{R}$ with
$\mathsf{W}$, and $\mathsf{R}^*$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [GJ08] -/
abbrev Logic.ILP₀ : Logic α := Logic.ofAxioms {Axioms.P₀ A B | (A) (B)}

notation "𝐈𝐋𝐏₀" => Logic.ILP₀

/-- - [GJ11] -/
abbrev Logic.ILR : Logic α := Logic.ofAxioms {Axioms.R A B C | (A) (B) (C)}

notation "𝐈𝐋𝐑" => Logic.ILR

abbrev Logic.ILRW : Logic α :=
  Logic.ofAxioms ({Axioms.R A B C | (A) (B) (C)} ∪ {Axioms.W A B | (A) (B)})

notation "𝐈𝐋𝐑𝐖" => Logic.ILRW

/-- - [GJ11] -/
abbrev Logic.ILRStar : Logic α := Logic.ofAxioms {Axioms.Rstar A B C | (A) (B) (C)}

notation "𝐈𝐋𝐑*" => Logic.ILRStar

namespace Logic

open ofAxioms

variable {A B C : Formula α}

@[simp] lemma ILP₀.axiomP₀ : 𝐈𝐋𝐏₀ ⊢ Axioms.P₀ A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILR.axiomR : 𝐈𝐋𝐑 ⊢ Axioms.R A B C := axm ⟨A, B, C, rfl⟩

@[simp] lemma ILRW.axiomR : 𝐈𝐋𝐑𝐖 ⊢ Axioms.R A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma ILRW.axiomW : 𝐈𝐋𝐑𝐖 ⊢ Axioms.W A B := axm <| .inr ⟨A, B, rfl⟩

@[simp] lemma ILRStar.axiomRstar : 𝐈𝐋𝐑* ⊢ Axioms.Rstar A B C := axm ⟨A, B, C, rfl⟩

lemma ILR.axiomM₀ : 𝐈𝐋𝐑 ⊢ Axioms.M₀ A B C := by
  have h₁ : 𝐈𝐋𝐑 ⊢ A ▷ ∼C 🡒 ∼□(∼A) 🡒 ∼□(∼∼C) := axiomJ4;
  have h₂ : 𝐈𝐋𝐑 ⊢ □C 🡒 □(∼∼C) := box_mono dni;
  have h₃ : 𝐈𝐋𝐑 ⊢ ∼□(∼A) ⋏ □C 🡒 ∼(A ▷ ∼C) := by cl_prover [h₁, h₂];
  have h₄ : 𝐈𝐋𝐑 ⊢ (◇A ⋏ □C) ▷ ∼(A ▷ ∼C) := rhd_of_provable h₃;
  have h₅ : 𝐈𝐋𝐑 ⊢ Axioms.J2 (◇A ⋏ □C) (∼(A ▷ ∼C)) (B ⋏ □C) := axiomJ2;
  cl_prover [axiomR (A := A) (B := B) (C := C), h₄, h₅];

/-- - [GJ11] -/
lemma ILR.axiomP₀ : 𝐈𝐋𝐑 ⊢ Axioms.P₀ A B := by
  have h₁ : 𝐈𝐋𝐑 ⊢ ∼□(∼B) ⋏ □(∼B) 🡒 ⊥ := by cl_prover;
  have h₂ : 𝐈𝐋𝐑 ⊢ ∼(A ▷ ∼∼B) ▷ (◇B ⋏ □(∼B)) 🡒 ∼(A ▷ ∼∼B) ▷ ⊥ := rhd_mono_right h₁;
  have h₃ : 𝐈𝐋𝐑 ⊢ ∼(A ▷ ∼∼B) ▷ ⊥ 🡒 □(∼∼(A ▷ ∼∼B)) := rhd_bot;
  have h₄ : 𝐈𝐋𝐑 ⊢ A ▷ ∼∼B 🡒 A ▷ B := rhd_mono_right Entailment.dne;
  have h₅ : 𝐈𝐋𝐑 ⊢ ∼∼(A ▷ ∼∼B) 🡒 A ▷ B := by cl_prover [h₄];
  cl_prover [axiomR (A := A) (B := ◇B) (C := ∼B), h₂, h₃, box_mono h₅];

lemma ILRW.axiomRstar : 𝐈𝐋𝐑𝐖 ⊢ Axioms.Rstar A B C := by
  have h : 𝐈𝐋𝐑𝐖 ⊢
      ∼(A ▷ ∼C) ▷ ((B ⋏ □(∼A)) ⋏ □C) 🡒 ∼(A ▷ ∼C) ▷ (B ⋏ □C ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  cl_prover [axiomW (A := A) (B := B), axiomR (A := A) (B := B ⋏ □(∼A)) (C := C), h];

lemma ILRStar.axiomR : 𝐈𝐋𝐑* ⊢ Axioms.R A B C := by
  have h : 𝐈𝐋𝐑* ⊢ ∼(A ▷ ∼C) ▷ (B ⋏ □C ⋏ □(∼A)) 🡒 ∼(A ▷ ∼C) ▷ (B ⋏ □C) :=
    rhd_mono_right (by cl_prover);
  cl_prover [axiomRstar (A := A) (B := B) (C := C), h];

/-- - [GJ11] -/
lemma ILRStar.axiomW : 𝐈𝐋𝐑* ⊢ Axioms.W A B := by
  have h₁ : 𝐈𝐋𝐑* ⊢ A ▷ ∼⊤ 🡒 ∼□(∼A) 🡒 ∼□(∼∼⊤) := axiomJ4;
  have h₂ : (𝐈𝐋𝐑* : Logic α) ⊢ ∼∼⊤ := by cl_prover;
  have h₃ : (𝐈𝐋𝐑* : Logic α) ⊢ □(∼∼⊤) := nec h₂;
  have h₄ : 𝐈𝐋𝐑* ⊢ ∼□(∼A) 🡒 ∼(A ▷ ∼⊤) := by cl_prover [h₁, h₃];
  have h₅ : 𝐈𝐋𝐑* ⊢ ◇A ▷ ∼(A ▷ ∼⊤) := rhd_of_provable h₄;
  have h₆ : 𝐈𝐋𝐑* ⊢ ∼(A ▷ ∼⊤) ▷ (B ⋏ □⊤ ⋏ □(∼A)) 🡒 ∼(A ▷ ∼⊤) ▷ (B ⋏ □(∼A)) :=
    rhd_mono_right (by cl_prover);
  have h₇ : 𝐈𝐋𝐑* ⊢ Axioms.J2 (◇A) (∼(A ▷ ∼⊤)) (B ⋏ □(∼A)) := axiomJ2;
  have h₈ : 𝐈𝐋𝐑* ⊢ Axioms.J3 (B ⋏ □(∼A)) (◇A) (B ⋏ □(∼A)) := axiomJ3;
  have h₉ : 𝐈𝐋𝐑* ⊢ B 🡒 B ⋏ □(∼A) ⋎ ∼□(∼A) := by cl_prover;
  have h₁₀ : 𝐈𝐋𝐑* ⊢ A ▷ B 🡒 A ▷ (B ⋏ □(∼A) ⋎ ◇A) := rhd_mono_right h₉;
  have h₁₁ : 𝐈𝐋𝐑* ⊢ Axioms.J2 A (B ⋏ □(∼A) ⋎ ◇A) (B ⋏ □(∼A)) := axiomJ2;
  have h₁₂ : 𝐈𝐋𝐑* ⊢ (B ⋏ □(∼A)) ▷ (B ⋏ □(∼A)) := rhd_refl;
  cl_prover [axiomRstar (A := A) (B := B) (C := ⊤), h₅, h₆, h₇, h₈, h₁₀, h₁₁, h₁₂];

instance : (𝐈𝐋𝐌₀ : Logic α) ⪯ 𝐈𝐋𝐑 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILR.axiomM₀

instance : (𝐈𝐋𝐏₀ : Logic α) ⪯ 𝐈𝐋𝐑 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILR.axiomP₀

instance : (𝐈𝐋𝐑 : Logic α) ⪯ 𝐈𝐋𝐑𝐖 := weakerThan_iff.mpr <| subset_of_subset Set.subset_union_left

instance : (𝐈𝐋𝐌₀𝐖 : Logic α) ⪯ 𝐈𝐋𝐑𝐖 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
  · exact subset_of_subset Set.subset_union_left ILR.axiomM₀
  · exact ILRW.axiomW

instance : (𝐈𝐋𝐑𝐖 : Logic α) ≊ 𝐈𝐋𝐑* := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
    · exact ILRStar.axiomR
    · exact ILRStar.axiomW)
  (subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILRW.axiomRstar)

end Logic

end FFL.InterpretabilityLogic

end
