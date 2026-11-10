module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic

/-!
# Extensions of $\mathbf{IL}^-$

This file defines the logic $\mathbf{IL}^-$, its named sublogics with their derived principles and
inclusions, and $\mathbf{CL}$. The framework `ofAxiomsMinus` and the axiom schemata are in `Logic`.
-/

@[expose] public section


namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [KO21, Definition 2.1] -/
abbrev Logic.ILMinus : Logic α := ofAxiomsMinus ∅

notation "𝐈𝐋⁻" => Logic.ILMinus

namespace Logic.ofAxiomsMinus

variable {𝔸 : FormulaSet α}

instance : (𝐈𝐋⁻ : Logic α) ⪯ ofAxiomsMinus 𝔸 :=
  weakerThan_iff.mpr <| subset_of_subset (Set.empty_subset _)

end Logic.ofAxiomsMinus


/-! ### Named logics -/

namespace Logic

/-- $\mathbf{IL}^-(\mathbf{J1})$.

- [KO21, §3.1]
-/
abbrev ILMinusJ1 : Logic α := ofAxiomsMinus {Axioms.J1 A B | (A) (B)}

/-- $\mathbf{IL}^-(\mathbf{J2})$.

- [KO21, §3.3]
-/
abbrev ILMinusJ2 : Logic α := ofAxiomsMinus {Axioms.J2 A B C | (A) (B) (C)}

/-- $\mathbf{IL}^-(\mathbf{J2}^+)$.

- [KO21, §3.3]
-/
abbrev ILMinusJ2Plus : Logic α := ofAxiomsMinus {Axioms.J2Plus A B C | (A) (B) (C)}

/-- $\mathbf{IL}^-(\mathbf{J4})$.

- [KO21, §3.2]
-/
abbrev ILMinusJ4 : Logic α := ofAxiomsMinus {Axioms.J4 A B | (A) (B)}

/-- $\mathbf{IL}^-(\mathbf{J4}^+)$.

- [KO21, §3.2]
-/
abbrev ILMinusJ4Plus : Logic α := ofAxiomsMinus {Axioms.J4Plus A B C | (A) (B) (C)}

/-- $\mathbf{IL}^-(\mathbf{J5})$.

- [KO21, §3.4]
-/
abbrev ILMinusJ5 : Logic α := ofAxiomsMinus {Axioms.J5 A | A}

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ1J5 : Logic α := ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J4}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ4PlusJ5 : Logic α :=
  ofAxiomsMinus ({Axioms.J4Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+)$.

- [KO21, §3]
-/
abbrev ILMinusJ1J4Plus : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)})

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ1J4PlusJ5 : Logic α :=
  ofAxiomsMinus
    ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J2}^+, \mathbf{J5})$.

- [KO21, §3]
-/
abbrev ILMinusJ2PlusJ5 : Logic α :=
  ofAxiomsMinus ({Axioms.J2Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J4}^+)$.

- [KO21, §6]
-/
abbrev ILMinusJ2J4Plus : Logic α :=
  ofAxiomsMinus ({Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)})

/-- $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev ILMinusJ2J5 : Logic α := ofAxiomsMinus ({Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J2}, \mathbf{J4}^+, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev ILMinusJ2J4PlusJ5 : Logic α :=
  ofAxiomsMinus
    ({Axioms.J2 A B C | (A) (B) (C)} ∪ {Axioms.J4Plus A B C | (A) (B) (C)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J4}, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev ILMinusJ4J5 : Logic α := ofAxiomsMinus ({Axioms.J4 A B | (A) (B)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4})$.

- [KO21, §6]
-/
abbrev ILMinusJ1J4 : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4 A B | (A) (B)})

/-- $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J4}, \mathbf{J5})$.

- [KO21, §6]
-/
abbrev ILMinusJ1J4J5 : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J4 A B | (A) (B)} ∪ {Axioms.J5 A | A})

/-- $\mathbf{CL}$, presented as $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J2})$.

- [KO21, Proposition 3.21]
-/
abbrev CL : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)})

notation "𝐂𝐋" => Logic.CL

end Logic

/-! ### Inclusions by axioms -/

namespace Logic

open ofAxiomsMinus

instance : (ILMinusJ2 : Logic α) ⪯ 𝐂𝐋 := weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1 : Logic α) ⪯ 𝐂𝐋 := weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1 : Logic α) ⪯ ILMinusJ1J4Plus :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ1J4Plus :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1 : Logic α) ⪯ ILMinusJ1J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ1J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ2Plus : Logic α) ⪯ ILMinusJ2PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ2PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1J4Plus : Logic α) ⪯ ILMinusJ1J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1J5 : Logic α) ⪯ ILMinusJ1J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4PlusJ5 : Logic α) ⪯ ILMinusJ1J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1 : Logic α) ⪯ ILMinusJ1J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ1J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ2 : Logic α) ⪯ ILMinusJ2J4Plus :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ2 : Logic α) ⪯ ILMinusJ2J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ2 : Logic α) ⪯ ILMinusJ2J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ2J4Plus :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ2J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ2J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ2J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ5 : Logic α) ⪯ ILMinusJ1J4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ1J4 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ1J4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1 : Logic α) ⪯ ILMinusJ1J4 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1 : Logic α) ⪯ ILMinusJ1J4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ2J4Plus : Logic α) ⪯ ILMinusJ2J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ2J5 : Logic α) ⪯ ILMinusJ2J4PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ4J5 : Logic α) ⪯ ILMinusJ1J4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

instance : (ILMinusJ1J4 : Logic α) ⪯ ILMinusJ1J4J5 :=
  weakerThan_iff.mpr <| subset_of_subset (by tauto_set)

end Logic

/-! ### Derived principles -/

namespace Logic

open ofAxiomsMinus

variable {A B C : Formula α}

namespace ILMinusJ1

@[simp] lemma axiomJ1 : ILMinusJ1 ⊢ Axioms.J1 A B := axm (by simp)

/-- - [KO21, Proposition 3.1] -/
@[simp] lemma axiomJ1' : ILMinusJ1 ⊢ Axioms.J1' A := by
  have : ILMinusJ1 ⊢ A 🡒 A := C_id;
  exact axiomJ1 ⨀ nec this;

end ILMinusJ1

namespace ILMinusJ2

@[simp] lemma axiomJ2 : ILMinusJ2 ⊢ Axioms.J2 A B C := axm (by simp)

/-- - [KO21, Corollary 3.5] -/
@[simp] lemma axiomJ4 : ILMinusJ2 ⊢ Axioms.J4 A B := by
  have h₁ : ILMinusJ2 ⊢ A ▷ B ⋏ B ▷ ⊥ 🡒 A ▷ ⊥ := axiomJ2;
  have h₂ : ILMinusJ2 ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) := dia_imp_dia_iff;
  cl_prover [h₁, h₂];

end ILMinusJ2

namespace ILMinusJ2Plus

@[simp] lemma axiomJ2Plus : ILMinusJ2Plus ⊢ Axioms.J2Plus A B C := axm (by simp)

/-- - [KO21, Proposition 3.12.1] -/
@[simp] lemma axiomJ2 : ILMinusJ2Plus ⊢ Axioms.J2 A B C := J2_of_J2Plus ⨀ axiomJ2Plus

/-- - [KO21, Proposition 3.13] -/
@[simp] lemma axiomJ4Plus : ILMinusJ2Plus ⊢ Axioms.J4Plus A B C := by
  have h₁ : ILMinusJ2Plus ⊢ □(A 🡒 B) 🡒 □(∼(A ⋏ ∼B)) := box_mono (by cl_prover);
  have h₂ : ILMinusJ2Plus ⊢ □(∼(A ⋏ ∼B)) 🡒 (A ⋏ ∼B) ▷ B := rhd_of_box_neg;
  have h₃ : ILMinusJ2Plus ⊢ C ▷ A 🡒 C ▷ (A ⋏ ∼B ⋎ B) := rhd_mono_right (by cl_prover);
  have h₄ : ILMinusJ2Plus ⊢ C ▷ (A ⋏ ∼B ⋎ B) ⋏ (A ⋏ ∼B) ▷ B 🡒 C ▷ B := axiomJ2Plus;
  cl_prover [h₁, h₂, h₃, h₄];

end ILMinusJ2Plus

namespace ILMinusJ4

@[simp] lemma axiomJ4 : ILMinusJ4 ⊢ Axioms.J4 A B := axm (by simp)

end ILMinusJ4

namespace ILMinusJ4Plus

@[simp] lemma axiomJ4Plus : ILMinusJ4Plus ⊢ Axioms.J4Plus A B C := axm (by simp)

/-- - [KO21, Proposition 3.7] -/
@[simp] lemma axiomJ4 : ILMinusJ4Plus ⊢ Axioms.J4 A B := by
  have h₁ : ILMinusJ4Plus ⊢ □(∼B) 🡘 B ▷ ⊥ := box_neg_iff_rhd_bot;
  have h₂ : ILMinusJ4Plus ⊢ □(B 🡒 ⊥) 🡒 A ▷ B 🡒 A ▷ ⊥ := axiomJ4Plus;
  have h₃ : ILMinusJ4Plus ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) := dia_imp_dia_iff;
  cl_prover [h₁, h₂, h₃];

end ILMinusJ4Plus

namespace ILMinusJ5

@[simp] lemma axiomJ5 : ILMinusJ5 ⊢ Axioms.J5 A := axm (by simp)

end ILMinusJ5

namespace CL

@[simp] lemma axiomJ1 : 𝐂𝐋 ⊢ Axioms.J1 A B := axm (by simp)

@[simp] lemma axiomJ2 : 𝐂𝐋 ⊢ Axioms.J2 A B C := axm (by simp)

/-- - [KO21, Proposition 3.12.2] -/
@[simp] lemma axiomJ2Plus : 𝐂𝐋 ⊢ Axioms.J2Plus A B C := by
  have h₁ : 𝐂𝐋 ⊢ B ▷ C ⋏ C ▷ C 🡒 (B ⋎ C) ▷ C := axiomJ3;
  have h₂ : 𝐂𝐋 ⊢ C ▷ C := WeakerThan.pbl (𝓢 := ILMinusJ1) (by simp);
  have h₃ : 𝐂𝐋 ⊢ A ▷ (B ⋎ C) ⋏ (B ⋎ C) ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h₁, h₂, h₃];

end CL

/-! ### Inclusions by derived principles -/

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ2 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; simp

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ4Plus :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, rfl⟩; simp

instance : (ILMinusJ2 : Logic α) ⪯ ILMinusJ2Plus :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; simp

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ2Plus :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; simp

instance : (ILMinusJ2Plus : Logic α) ⪯ 𝐂𝐋 :=
  weakerThan_iff.mpr <| subset_of_provable <| by rintro _ ⟨A, B, C, rfl⟩; simp

instance : (ILMinusJ4Plus : Logic α) ⪯ 𝐂𝐋 :=
  WeakerThan.trans (𝓣 := ILMinusJ2Plus) inferInstance inferInstance

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ2PlusJ5 :=
  WeakerThan.trans (𝓣 := ILMinusJ2Plus) inferInstance inferInstance

instance : (ILMinusJ4Plus : Logic α) ⪯ ILMinusJ1J4PlusJ5 :=
  WeakerThan.trans (𝓣 := ILMinusJ1J4Plus) inferInstance inferInstance

/-- - [KO21, Corollary 3.14] -/
@[simp] lemma CL.axiomJ4Plus : 𝐂𝐋 ⊢ Axioms.J4Plus A B C :=
  WeakerThan.pbl (𝓢 := ILMinusJ2Plus) (by simp)

@[simp] lemma CL.axiomJ4 : 𝐂𝐋 ⊢ Axioms.J4 A B := WeakerThan.pbl (𝓢 := ILMinusJ2) (by simp)

instance : (ILMinusJ1J4Plus : Logic α) ⪯ 𝐂𝐋 :=
  weakerThan_iff.mpr <| subset_of_provable <| by
    rintro _ (⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩) <;> simp

instance : (ILMinusJ4PlusJ5 : Logic α) ⪯ ILMinusJ2PlusJ5 :=
  weakerThan_iff.mpr <| subset_of_provable <| by
    rintro _ (⟨A, B, C, rfl⟩ | ⟨A, rfl⟩);
    · exact WeakerThan.pbl (𝓢 := ILMinusJ2Plus) (by simp);
    · exact axm (by simp);

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ2J4Plus :=
  WeakerThan.trans (𝓣 := ILMinusJ2) inferInstance inferInstance

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ2J5 :=
  WeakerThan.trans (𝓣 := ILMinusJ2) inferInstance inferInstance

instance : (ILMinusJ4 : Logic α) ⪯ ILMinusJ2J4PlusJ5 :=
  WeakerThan.trans (𝓣 := ILMinusJ2) inferInstance inferInstance

/-! ### Equivalent axiomatizations -/

/-- - [KO21, Proposition 3.1] -/
theorem ILMinusJ1.eq_ofAxiomsMinus_J1' :
    (ILMinusJ1 : Logic α) = ofAxiomsMinus {Axioms.J1' A | A} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J1' A | A} ⊢ □(A 🡒 B) 🡒 B ▷ B 🡒 A ▷ B :=
      rhd_anti_left_of_box;
    have h₂ : ofAxiomsMinus {Axioms.J1' A | A} ⊢ B ▷ B := axm (by simp);
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, rfl⟩;
    simp;

/-- - [KO21, Proposition 3.4] -/
theorem ILMinusJ4.eq_ofAxiomsMinus_J4' :
    (ILMinusJ4 : Logic α) = ofAxiomsMinus {Axioms.J4' A B | (A) (B)} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J4' A B | (A) (B)} ⊢ A ▷ B 🡒 B ▷ ⊥ 🡒 A ▷ ⊥ := axm (by simp);
    have h₂ : ofAxiomsMinus {Axioms.J4' A B | (A) (B)} ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) :=
      dia_imp_dia_iff;
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, B, rfl⟩;
    have h₁ : ILMinusJ4 ⊢ A ▷ B 🡒 ◇A 🡒 ◇B := ILMinusJ4.axiomJ4;
    have h₂ : ILMinusJ4 ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) := dia_imp_dia_iff;
    cl_prover [h₁, h₂];

section J4Plus

private lemma J4Plus'_subset :
    (ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} : Logic α) ⊆ ILMinusJ4Plus := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ILMinusJ4Plus ⊢ □A 🡒 □((A 🡒 B) 🡒 B) := box_mono (by cl_prover);
  have h₂ : ILMinusJ4Plus ⊢ □((A 🡒 B) 🡒 B) 🡒 C ▷ (A 🡒 B) 🡒 C ▷ B := ILMinusJ4Plus.axiomJ4Plus;
  cl_prover [h₁, h₂];

private lemma J4Plus''_subset :
    (ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} : Logic α) ⊆
      ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} ⊢
      C ▷ B 🡒 C ▷ (A 🡒 A ⋏ B) := rhd_mono_right (by cl_prover);
  have h₂ : ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} ⊢
      □A 🡒 C ▷ (A 🡒 A ⋏ B) 🡒 C ▷ (A ⋏ B) := axm (by simp);
  cl_prover [h₁, h₂];

private lemma J4Plus_subset :
    (ILMinusJ4Plus : Logic α) ⊆ ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} := by
  apply subset_of_provable;
  rintro _ ⟨A, B, C, rfl⟩;
  have h₁ : ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} ⊢
      □(A 🡒 B) 🡒 C ▷ A 🡒 C ▷ ((A 🡒 B) ⋏ A) := axm (by simp);
  have h₂ : ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} ⊢
      C ▷ ((A 🡒 B) ⋏ A) 🡒 C ▷ B := rhd_mono_right (by cl_prover);
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 3.6] -/
theorem ILMinusJ4Plus.eq_ofAxiomsMinus_J4Plus' :
    (ILMinusJ4Plus : Logic α) = ofAxiomsMinus {Axioms.J4Plus' A B C | (A) (B) (C)} :=
  Set.Subset.antisymm (J4Plus_subset.trans J4Plus''_subset) J4Plus'_subset

/-- - [KO21, Proposition 3.6] -/
theorem ILMinusJ4Plus.eq_ofAxiomsMinus_J4Plus'' :
    (ILMinusJ4Plus : Logic α) = ofAxiomsMinus {Axioms.J4Plus'' A B C | (A) (B) (C)} :=
  Set.Subset.antisymm J4Plus_subset (J4Plus''_subset.trans J4Plus'_subset)

end J4Plus

/-- - [KO21, Proposition 3.11] -/
theorem ILMinusJ2Plus.eq_ofAxiomsMinus_J2Plus' :
    (ILMinusJ2Plus : Logic α) = ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} := by
  apply Set.Subset.antisymm;
  · apply subset_of_provable;
    rintro _ ⟨A, B, C, rfl⟩;
    have h₁ : ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} ⊢
        B ▷ C 🡒 ((B ⋎ C) ⋏ ∼C) ▷ C := rhd_anti_left (by cl_prover);
    have h₂ : ofAxiomsMinus {Axioms.J2Plus' A B C | (A) (B) (C)} ⊢
        A ▷ (B ⋎ C) ⋏ ((B ⋎ C) ⋏ ∼C) ▷ C 🡒 A ▷ C := axm (by simp);
    cl_prover [h₁, h₂];
  · apply subset_of_provable;
    rintro _ ⟨A, B, C, rfl⟩;
    have h₁ : ILMinusJ2Plus ⊢ A ▷ B 🡒 A ▷ (B ⋏ ∼C ⋎ C) := rhd_mono_right (by cl_prover);
    have h₂ : ILMinusJ2Plus ⊢ A ▷ (B ⋏ ∼C ⋎ C) ⋏ (B ⋏ ∼C) ▷ C 🡒 A ▷ C :=
      ILMinusJ2Plus.axiomJ2Plus;
    cl_prover [h₁, h₂];

end Logic


end FFL.InterpretabilityLogic

