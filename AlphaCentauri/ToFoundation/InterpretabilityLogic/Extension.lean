module

public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Logic

/-!
# Extensions of $\mathbf{IL}$

The principles of interpretability logic beyond $\mathbf{IL}$, the extensions of $\mathbf{IL}$ by
them, and the inclusions and equivalences among these extensions.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment

variable {α : Type*}

/-! ### Principles beyond $\mathbf{IL}$ -/

namespace Axioms

variable (A B C : Formula α)

/-- Montagna's principle.

- [Vis88]
- [Vis90, §6.4]
-/
protected abbrev M : Formula α := A ▷ B 🡒 (A ⋏ □C) ▷ (B ⋏ □C)

/-- - [Vis97] -/
protected abbrev M₀ : Formula α := A ▷ B 🡒 (◇A ⋏ □C) ▷ (B ⋏ □C)

/-- The persistence principle.

- [Vis88]
- [Vis90, §6.3]
-/
protected abbrev P : Formula α := A ▷ B 🡒 □(A ▷ B)

/-- - [GJ08] -/
protected abbrev P₀ : Formula α := A ▷ ◇B 🡒 □(A ▷ B)

/-- The de Jongh–Visser principle.

- [Vis88]
- [Vis90, §6.2]
- [Sve91]
-/
protected abbrev W : Formula α := A ▷ B 🡒 A ▷ (B ⋏ □(∼A))

/-- - [Vis97] -/
protected abbrev Wstar : Formula α := A ▷ B 🡒 (B ⋏ □C) ▷ (B ⋏ □C ⋏ □(∼A))

/-- - [Sve91] -/
protected abbrev KW1Zero : Formula α := (B ⋏ A) ▷ ◇B 🡒 B ▷ (B ⋏ ∼A)

/-- - [Vis97] -/
protected abbrev KW2 : Formula α := A ▷ ◇B 🡒 B ▷ (B ⋏ ∼A)

/-- Feferman's principle.

- [Vis90, §6.2.1]
- [Sve91]
-/
protected abbrev F : Formula α := A ▷ ◇A 🡒 □(∼A)

/-- - [GJ11] -/
protected abbrev R : Formula α := A ▷ B 🡒 ∼(A ▷ ∼C) ▷ (B ⋏ □C)

/-- - [GJ11] -/
protected abbrev Rstar : Formula α := A ▷ B 🡒 ∼(A ▷ ∼C) ▷ (B ⋏ □C ⋏ □(∼A))

end Axioms

/-! ### Theorems of $\mathbf{IL}$ -/

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {A B C : Formula α}

lemma rhd_of_provable (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h

lemma rhd_refl : ofAxioms 𝔸 ⊢ A ▷ A := rhd_of_provable C_id

/-- - [Vis90, §6.1.1] -/
lemma rhd_and_box_neg : ofAxioms 𝔸 ⊢ A ▷ (A ⋏ □(∼A)) := by
  have h₁ : ofAxioms 𝔸 ⊢ ∼(A ⋏ □(∼A)) 🡒 □(∼A) 🡒 ∼A := by cl_prover;
  have h₂ : ofAxioms 𝔸 ⊢ □(□(∼A) 🡒 ∼A) 🡒 □(∼A) := axiomL;
  have h₃ : ofAxioms 𝔸 ⊢ A 🡒 A ⋏ □(∼A) ⋎ ∼□(∼(A ⋏ □(∼A))) := by
    cl_prover [box_mono h₁, h₂];
  have h₄ : ofAxioms 𝔸 ⊢ ∼□(∼(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) := axiomJ5;
  have h₅ : ofAxioms 𝔸 ⊢ Axioms.J3 (A ⋏ □(∼A)) (∼□(∼(A ⋏ □(∼A)))) (A ⋏ □(∼A)) := axiomJ3;
  have h₆ : ofAxioms 𝔸 ⊢ Axioms.J2 A (A ⋏ □(∼A) ⋎ ∼□(∼(A ⋏ □(∼A)))) (A ⋏ □(∼A)) := axiomJ2;
  cl_prover [rhd_of_provable h₃, rhd_refl (𝔸 := 𝔸) (A := A ⋏ □(∼A)), h₄, h₅, h₆];

/-- - [Vis90, §6.1.1] -/
lemma rhd_bot : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼A) := by
  have h₁ : ofAxioms 𝔸 ⊢ ∼⊥ := by cl_prover;
  have h₂ : ofAxioms 𝔸 ⊢ □(∼⊥) := nec h₁;
  have h₃ : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 ∼□(∼A) 🡒 ∼□(∼⊥) := axiomJ4;
  cl_prover [h₂, h₃];


lemma rhd_and_not_rhd_neg : ofAxioms 𝔸 ⊢ A ▷ B ⋏ ∼(A ▷ ∼C) 🡒 ◇(B ⋏ □C) := by
  have h₀ : ofAxioms 𝔸 ⊢ □(∼∼C) 🡒 □C := box_mono dne;
  have h₁ : ofAxioms 𝔸 ⊢ ∼(B ⋏ □C) 🡒 B 🡒 ∼□(∼∼C) := by cl_prover [h₀];
  have h₂ : ofAxioms 𝔸 ⊢ □(B 🡒 ∼□(∼∼C)) 🡒 B ▷ ◇(∼C) := axiomJ1;
  have h₃ : ofAxioms 𝔸 ⊢ ◇(∼C) ▷ ∼C := axiomJ5;
  have h₄ : ofAxioms 𝔸 ⊢ Axioms.J2 B (◇(∼C)) (∼C) := axiomJ2;
  have h₅ : ofAxioms 𝔸 ⊢ Axioms.J2 A B (∼C) := axiomJ2;
  have : ofAxioms 𝔸 ⊢ A ▷ B ⋏ ∼(A ▷ ∼C) 🡒 ∼□(∼(B ⋏ □C)) := by
    cl_prover [box_mono h₁, h₂, h₃, h₄, h₅];
  exact this;

end Logic.ofAxioms

/-! ### Extensions of $\mathbf{IL}$ -/

/-- - [Vis97] -/
abbrev Logic.ILM₀ : Logic α := Logic.ofAxioms {Axioms.M₀ A B C | (A) (B) (C)}

notation "𝐈𝐋𝐌₀" => Logic.ILM₀

/-- - [Vis90, §6.4] -/
abbrev Logic.ILM : Logic α := Logic.ofAxioms {Axioms.M A B C | (A) (B) (C)}

notation "𝐈𝐋𝐌" => Logic.ILM

/-- - [GJ08] -/
abbrev Logic.ILP₀ : Logic α := Logic.ofAxioms {Axioms.P₀ A B | (A) (B)}

notation "𝐈𝐋𝐏₀" => Logic.ILP₀

/-- - [Vis90, §6.3] -/
abbrev Logic.ILP : Logic α := Logic.ofAxioms {Axioms.P A B | (A) (B)}

notation "𝐈𝐋𝐏" => Logic.ILP

/-- - [Vis90, §6.2] -/
abbrev Logic.ILW : Logic α := Logic.ofAxioms {Axioms.W A B | (A) (B)}

notation "𝐈𝐋𝐖" => Logic.ILW

/-- - [Vis97] -/
abbrev Logic.ILWStar : Logic α := Logic.ofAxioms {Axioms.Wstar A B C | (A) (B) (C)}

notation "𝐈𝐋𝐖*" => Logic.ILWStar

abbrev Logic.ILM₀W : Logic α :=
  Logic.ofAxioms ({Axioms.M₀ A B C | (A) (B) (C)} ∪ {Axioms.W A B | (A) (B)})

notation "𝐈𝐋𝐌₀𝐖" => Logic.ILM₀W

/-- - [Sve91] -/
abbrev Logic.ILF : Logic α := Logic.ofAxioms {Axioms.F A | (A)}

notation "𝐈𝐋𝐅" => Logic.ILF

/-- - [Sve91] -/
abbrev Logic.ILKW1Zero : Logic α := Logic.ofAxioms {Axioms.KW1Zero A B | (A) (B)}

notation "𝐈𝐋𝐊𝐖𝟏⁰" => Logic.ILKW1Zero

/-- - [Vis97] -/
abbrev Logic.ILKW2 : Logic α := Logic.ofAxioms {Axioms.KW2 A B | (A) (B)}

notation "𝐈𝐋𝐊𝐖𝟐" => Logic.ILKW2

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

@[simp] lemma ILM₀.axiomM₀ : 𝐈𝐋𝐌₀ ⊢ Axioms.M₀ A B C := axm ⟨A, B, C, rfl⟩

@[simp] lemma ILM.axiomM : 𝐈𝐋𝐌 ⊢ Axioms.M A B C := axm ⟨A, B, C, rfl⟩

@[simp] lemma ILP₀.axiomP₀ : 𝐈𝐋𝐏₀ ⊢ Axioms.P₀ A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILP.axiomP : 𝐈𝐋𝐏 ⊢ Axioms.P A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILW.axiomW : 𝐈𝐋𝐖 ⊢ Axioms.W A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILWStar.axiomWstar : 𝐈𝐋𝐖* ⊢ Axioms.Wstar A B C := axm ⟨A, B, C, rfl⟩

@[simp] lemma ILM₀W.axiomM₀ : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.M₀ A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma ILM₀W.axiomW : 𝐈𝐋𝐌₀𝐖 ⊢ Axioms.W A B := axm <| .inr ⟨A, B, rfl⟩

@[simp] lemma ILF.axiomF : 𝐈𝐋𝐅 ⊢ Axioms.F A := axm ⟨A, rfl⟩

@[simp] lemma ILKW1Zero.axiomKW1Zero : 𝐈𝐋𝐊𝐖𝟏⁰ ⊢ Axioms.KW1Zero A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILKW2.axiomKW2 : 𝐈𝐋𝐊𝐖𝟐 ⊢ Axioms.KW2 A B := axm ⟨A, B, rfl⟩

@[simp] lemma ILR.axiomR : 𝐈𝐋𝐑 ⊢ Axioms.R A B C := axm ⟨A, B, C, rfl⟩

@[simp] lemma ILRW.axiomR : 𝐈𝐋𝐑𝐖 ⊢ Axioms.R A B C := axm <| .inl ⟨A, B, C, rfl⟩

@[simp] lemma ILRW.axiomW : 𝐈𝐋𝐑𝐖 ⊢ Axioms.W A B := axm <| .inr ⟨A, B, rfl⟩

@[simp] lemma ILRStar.axiomRstar : 𝐈𝐋𝐑* ⊢ Axioms.Rstar A B C := axm ⟨A, B, C, rfl⟩

/-! ### Derived principles -/

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

/-! ### Inclusions -/

instance {𝔸 : Set (Formula α)} : (𝐈𝐋 : Logic α) ⪯ ofAxioms 𝔸 := weakerThan_iff.mpr IL_subset

instance : (𝐈𝐋𝐅 : Logic α) ⪯ 𝐈𝐋𝐊𝐖𝟐 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, rfl⟩; exact ILKW2.axiomF

instance : (𝐈𝐋𝐊𝐖𝟏⁰ : Logic α) ≊ 𝐈𝐋𝐊𝐖𝟐 := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILKW2.axiomKW1Zero)
  (subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILKW1Zero.axiomKW2)

instance : (𝐈𝐋𝐊𝐖𝟐 : Logic α) ⪯ 𝐈𝐋𝐖 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILW.axiomKW2

instance : (𝐈𝐋𝐖 : Logic α) ⪯ 𝐈𝐋𝐖* :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; exact ILWStar.axiomW

instance : (𝐈𝐋𝐖* : Logic α) ≊ 𝐈𝐋𝐌₀𝐖 := equiv_iff.mpr <| subset_antisymm
  (subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; exact ILM₀W.axiomWstar)
  (subset_of_provable <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
    · exact ILWStar.axiomM₀
    · exact ILWStar.axiomW)

instance : (𝐈𝐋𝐌₀ : Logic α) ⪯ 𝐈𝐋𝐌₀𝐖 := weakerThan_iff.mpr <| subset_of_subset Set.subset_union_left

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

instance : (𝐈𝐋𝐑𝐖 : Logic α) ⪯ 𝐈𝐋𝐌 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
  · exact ILM.axiomR
  · exact ILM.axiomW

instance : (𝐈𝐋𝐑𝐖 : Logic α) ⪯ 𝐈𝐋𝐏 := weakerThan_iff.mpr <| subset_of_provable <| by
  rintro _ (⟨A, B, C, rfl⟩ | ⟨A, B, rfl⟩)
  · exact ILP.axiomR
  · exact ILP.axiomW

end Logic

end FFL.InterpretabilityLogic

end
