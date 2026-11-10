module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic

/-!
# Extensions of $\mathbf{IL}^-$

This file keeps the framework `ofAxiomsMinus`, the logic $\mathbf{IL}^-$, the named sublogics of
$\mathbf{IL}^-$ with their derived principles and inclusions, and $\mathbf{CL}$ in one place. The
completeness constructions in `Veltman` and `Verbrugge` refer to these names and to their derived
principles, so the definitions cannot move into the files that state soundness and completeness
without creating an import cycle. Those files are `Logic/ILMinus/<sublogic>.lean`.
-/

@[expose] public section


namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-! ### Axioms -/

namespace Axioms

variable (A B C : Formula α)

/-- - [KO21, §3.1] -/
protected abbrev J1' : Formula α := A ▷ A

/-- - [KO21, §3.3] -/
protected abbrev J2Plus : Formula α := A ▷ (B ⋎ C) ⋏ B ▷ C 🡒 A ▷ C

/-- - [KO21, §3.3] -/
protected abbrev J2Plus' : Formula α := A ▷ B ⋏ (B ⋏ ∼C) ▷ C 🡒 A ▷ C

/-- - [KO21, §3.2] -/
protected abbrev J4' : Formula α := A ▷ B 🡒 B ▷ ⊥ 🡒 A ▷ ⊥

/-- - [KO21, §3.2] -/
protected abbrev J4Plus : Formula α := □(A 🡒 B) 🡒 C ▷ A 🡒 C ▷ B

/-- - [KO21, §3.2] -/
protected abbrev J4Plus' : Formula α := □A 🡒 C ▷ (A 🡒 B) 🡒 C ▷ B

/-- - [KO21, §3.2] -/
protected abbrev J4Plus'' : Formula α := □A 🡒 C ▷ B 🡒 C ▷ (A ⋏ B)

/-- - [KO21, Definition 2.1] -/
protected abbrev J6 : Formula α := □A 🡘 ∼A ▷ ⊥

end Axioms

/-! ### Extensions of $\mathbf{IL}^-$ -/

/-- The smallest logic containing `𝔸` and the axioms of $\mathbf{IL}^-$, closed under modus ponens,
necessitation, $\mathbf{R1}$ and $\mathbf{R2}$.

- [KO21, Definition 2.1]
-/
inductive Logic.ofAxiomsMinus (𝔸 : Set (Formula α)) : Logic α
  | axm {A}          : A ∈ 𝔸 → ofAxiomsMinus 𝔸 A
  | mdp {A B}        : ofAxiomsMinus 𝔸 (A 🡒 B) → ofAxiomsMinus 𝔸 A → ofAxiomsMinus 𝔸 B
  | nec {A}          : ofAxiomsMinus 𝔸 A → ofAxiomsMinus 𝔸 (□A)
  | rule1 {A B C}    : ofAxiomsMinus 𝔸 (A 🡒 B) → ofAxiomsMinus 𝔸 (C ▷ A 🡒 C ▷ B)
  | rule2 {A B C}    : ofAxiomsMinus 𝔸 (A 🡒 B) → ofAxiomsMinus 𝔸 (B ▷ C 🡒 A ▷ C)
  | verum            : ofAxiomsMinus 𝔸 Axioms.Verum
  | implyK {A B}     : ofAxiomsMinus 𝔸 (Axioms.ImplyK A B)
  | implyS {A B C}   : ofAxiomsMinus 𝔸 (Axioms.ImplyS A B C)
  | andElimL {A B}   : ofAxiomsMinus 𝔸 (Axioms.AndElim₁ A B)
  | andElimR {A B}   : ofAxiomsMinus 𝔸 (Axioms.AndElim₂ A B)
  | andIntro {A B}   : ofAxiomsMinus 𝔸 (Axioms.AndInst A B)
  | orIntroL {A B}   : ofAxiomsMinus 𝔸 (Axioms.OrInst₁ A B)
  | orIntroR {A B}   : ofAxiomsMinus 𝔸 (Axioms.OrInst₂ A B)
  | orElim {A B C}   : ofAxiomsMinus 𝔸 (Axioms.OrElim A B C)
  | dne {A}          : ofAxiomsMinus 𝔸 (Axioms.DNE A)
  | axiomK {A B}     : ofAxiomsMinus 𝔸 (□(A 🡒 B) 🡒 □A 🡒 □B)
  | axiomL {A}       : ofAxiomsMinus 𝔸 (□(□A 🡒 A) 🡒 □A)
  | axiomJ3 {A B C}  : ofAxiomsMinus 𝔸 (Axioms.J3 A B C)
  | axiomJ6 {A}      : ofAxiomsMinus 𝔸 (Axioms.J6 A)

/-- - [KO21, Definition 2.1] -/
abbrev Logic.ILMinus : Logic α := ofAxiomsMinus ∅

notation "𝐈𝐋⁻" => Logic.ILMinus

namespace Logic.ofAxiomsMinus

variable {𝔸 𝔹 : Set (Formula α)}

instance : ModusPonens (ofAxiomsMinus 𝔸) := ⟨mdp⟩
instance : HasAxiomImplyK (ofAxiomsMinus 𝔸) := ⟨implyK⟩
instance : HasAxiomImplyS (ofAxiomsMinus 𝔸) := ⟨implyS⟩
instance : HasAxiomAndInst (ofAxiomsMinus 𝔸) := ⟨andIntro⟩

instance : Entailment.Minimal (ofAxiomsMinus 𝔸) where
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

instance : Entailment.Cl (ofAxiomsMinus 𝔸) where
  dne := dne

instance : (ofAxiomsMinus 𝔸).ExtendsGL := ⟨nec, axiomK, axiomL⟩

/-- `ofAxiomsMinus 𝔸` is contained in every extension of $\mathbf{IL}^-$ that proves `𝔸`. -/
lemma subset_of_provable (h : ∀ A ∈ 𝔸, ofAxiomsMinus 𝔹 ⊢ A) :
    ofAxiomsMinus 𝔸 ⊆ ofAxiomsMinus 𝔹 := by
  intro A hA;
  induction hA with
  | axm hA => exact h _ hA;
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
  | nec _ ih => exact nec ih;
  | rule1 _ ih => exact rule1 ih;
  | rule2 _ ih => exact rule2 ih;
  | verum => exact verum;
  | implyK => exact implyK;
  | implyS => exact implyS;
  | andElimL => exact andElimL;
  | andElimR => exact andElimR;
  | andIntro => exact andIntro;
  | orIntroL => exact orIntroL;
  | orIntroR => exact orIntroR;
  | orElim => exact orElim;
  | dne => exact dne;
  | axiomK => exact axiomK;
  | axiomL => exact axiomL;
  | axiomJ3 => exact axiomJ3;
  | axiomJ6 => exact axiomJ6;

lemma subset_of_subset (h : 𝔸 ⊆ 𝔹) : ofAxiomsMinus 𝔸 ⊆ ofAxiomsMinus 𝔹 :=
  subset_of_provable fun _ hA ↦ axm (h hA)

instance : (𝐈𝐋⁻ : Logic α) ⪯ ofAxiomsMinus 𝔸 :=
  weakerThan_iff.mpr <| subset_of_subset (Set.empty_subset _)

variable {A B C : Formula α}

lemma rhd_mono_right (h : ofAxiomsMinus 𝔸 ⊢ A 🡒 B) : ofAxiomsMinus 𝔸 ⊢ C ▷ A 🡒 C ▷ B := rule1 h

lemma rhd_anti_left (h : ofAxiomsMinus 𝔸 ⊢ A 🡒 B) : ofAxiomsMinus 𝔸 ⊢ B ▷ C 🡒 A ▷ C := rule2 h

lemma box_neg_iff_rhd_bot : ofAxiomsMinus 𝔸 ⊢ □(∼A) 🡘 A ▷ ⊥ := by
  have h₁ : ofAxiomsMinus 𝔸 ⊢ □(∼A) 🡘 ∼∼A ▷ ⊥ := axiomJ6;
  have h₂ : ofAxiomsMinus 𝔸 ⊢ ∼∼A ▷ ⊥ 🡒 A ▷ ⊥ := rhd_anti_left dni;
  have h₃ : ofAxiomsMinus 𝔸 ⊢ A ▷ ⊥ 🡒 ∼∼A ▷ ⊥ := rhd_anti_left dne;
  cl_prover [h₁, h₂, h₃];

/-- - [KO21, Proposition 2.5.1] -/
lemma rhd_of_box_neg : ofAxiomsMinus 𝔸 ⊢ □(∼A) 🡒 A ▷ B := by
  have h₁ : ofAxiomsMinus 𝔸 ⊢ □(∼A) 🡘 A ▷ ⊥ := box_neg_iff_rhd_bot;
  have h₂ : ofAxiomsMinus 𝔸 ⊢ A ▷ ⊥ 🡒 A ▷ B := rhd_mono_right efq;
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 2.5.2] -/
lemma rhd_anti_left_of_box : ofAxiomsMinus 𝔸 ⊢ □(A 🡒 B) 🡒 B ▷ C 🡒 A ▷ C := by
  have h₁ : ofAxiomsMinus 𝔸 ⊢ □(A 🡒 B) 🡒 □(∼(A ⋏ ∼B)) := box_mono (by cl_prover);
  have h₂ : ofAxiomsMinus 𝔸 ⊢ □(∼(A ⋏ ∼B)) 🡒 (A ⋏ ∼B) ▷ C := rhd_of_box_neg;
  have h₃ : ofAxiomsMinus 𝔸 ⊢ (A ⋏ ∼B) ▷ C ⋏ B ▷ C 🡒 (A ⋏ ∼B ⋎ B) ▷ C := axiomJ3;
  have h₄ : ofAxiomsMinus 𝔸 ⊢ (A ⋏ ∼B ⋎ B) ▷ C 🡒 A ▷ C := rhd_anti_left (by cl_prover);
  cl_prover [h₁, h₂, h₃, h₄];

/-- - [KO21, Proposition 3.4] -/
lemma dia_imp_dia_iff : ofAxiomsMinus 𝔸 ⊢ (◇A 🡒 ◇B) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥) := by
  have h₁ : ofAxiomsMinus 𝔸 ⊢ □(∼A) 🡘 A ▷ ⊥ := box_neg_iff_rhd_bot;
  have h₂ : ofAxiomsMinus 𝔸 ⊢ □(∼B) 🡘 B ▷ ⊥ := box_neg_iff_rhd_bot;
  change ofAxiomsMinus 𝔸 ⊢ (∼□(∼A) 🡒 ∼□(∼B)) 🡘 (B ▷ ⊥ 🡒 A ▷ ⊥);
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 3.12.1] -/
lemma J2_of_J2Plus : ofAxiomsMinus 𝔸 ⊢ Axioms.J2Plus A B C 🡒 Axioms.J2 A B C := by
  have : ofAxiomsMinus 𝔸 ⊢ A ▷ B 🡒 A ▷ (B ⋎ C) := rhd_mono_right or₁;
  cl_prover [this];

lemma fdisj_rhd [DecidableEq α] {X : Set (Formula α)} {𝒢 : Finset (Formula α)}
    (h : ∀ G ∈ 𝒢, X *⊢[ofAxiomsMinus 𝔸] G ▷ C) : X *⊢[ofAxiomsMinus 𝔸] 𝒢.disj ▷ C := by
  induction 𝒢 using Finset.induction_on with
  | empty => simpa using Context.of (rhd_of_box_neg (A := ⊥) (B := C) ⨀ provable_box verum);
  | insert G 𝒢 _ ih =>
    have h₁ : X *⊢[ofAxiomsMinus 𝔸] (G ⋎ 𝒢.disj) ▷ C :=
      Context.of axiomJ3 ⨀ K_intro (h G (by simp)) (ih fun H hH ↦ h H (by simp [hH]));
    exact Context.of (rhd_anti_left CinsertFDisjAFDisj) ⨀ h₁;

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

end
