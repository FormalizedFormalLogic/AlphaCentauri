module

public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Formula
public import Foundation.Propositional.Entailment.Cl
public import Foundation.Meta.ClProver

/-!
# Interpretability logics

A logic is a set of formulas, regarded as an `Entailment` via membership. Every logic here extends
$\mathbf{IL}^-$: it is the smallest set containing a set of axioms together with those of
$\mathbf{IL}^-$ and closed under modus ponens, necessitation and the rules $\mathbf{R1}$ and
$\mathbf{R2}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

abbrev Logic (α : Type*) := Set (Formula α)

open Entailment Formula

variable {α : Type*}

instance : Entailment (Logic α) (Formula α) := ⟨fun L A ↦ A ∈ L⟩

namespace Logic

variable {L L₁ L₂ : Logic α} {A : Formula α}

lemma provable_iff_mem : L ⊢ A ↔ A ∈ L := Iff.rfl

lemma weakerThan_iff : L₁ ⪯ L₂ ↔ L₁ ⊆ L₂ := ⟨fun h ↦ h.subset, fun h ↦ ⟨h⟩⟩

lemma strictlyWeakerThan_iff : L₁ ⪱ L₂ ↔ L₁ ⊂ L₂ :=
  ⟨fun h ↦ ⟨weakerThan_iff.mp h.weakerThan, fun h' ↦ h.notWT (weakerThan_iff.mpr h')⟩,
    fun h ↦ ⟨weakerThan_iff.mpr h.1, fun h' ↦ h.2 (weakerThan_iff.mp h')⟩⟩

lemma equiv_iff : L₁ ≊ L₂ ↔ L₁ = L₂ := ⟨fun h ↦ h.eq, fun h ↦ ⟨congrArg theory h⟩⟩

end Logic

/-! ### Axioms -/

namespace Axioms

variable (A B C : Formula α)

/-- - [KO21, §3.1] -/
protected abbrev J1 : Formula α := □(A 🡒 B) 🡒 A ▷ B

/-- - [KO21, §3.3] -/
protected abbrev J2 : Formula α := A ▷ B 🡒 B ▷ C 🡒 A ▷ C

/-- - [KO21, §3.3] -/
protected abbrev J2Plus : Formula α := A ▷ (B ⋎ C) 🡒 B ▷ C 🡒 A ▷ C

/-- - [KO21, Definition 2.1] -/
protected abbrev J3 : Formula α := A ▷ C 🡒 B ▷ C 🡒 (A ⋎ B) ▷ C

/-- - [KO21, §3.2] -/
protected abbrev J4 : Formula α := A ▷ B 🡒 ◇A 🡒 ◇B

/-- - [KO21, §3.2] -/
protected abbrev J4Plus : Formula α := □(A 🡒 B) 🡒 C ▷ A 🡒 C ▷ B

/-- - [KO21, §3.4] -/
protected abbrev J5 : Formula α := ◇A ▷ A

/-- - [KO21, Definition 2.1] -/
protected abbrev J6 : Formula α := □A 🡘 ∼A ▷ ⊥

end Axioms

/-! ### Extensions of $\mathbf{IL}^-$ -/

/-- The smallest logic containing `𝔸` and the axioms of $\mathbf{IL}^-$, closed under modus ponens,
necessitation, $\mathbf{R1}$ and $\mathbf{R2}$.

- [KO21, Definition 2.1]
-/
inductive Logic.ofAxioms (𝔸 : Set (Formula α)) : Logic α
  | axm {A}          : A ∈ 𝔸 → ofAxioms 𝔸 A
  | mdp {A B}        : ofAxioms 𝔸 (A 🡒 B) → ofAxioms 𝔸 A → ofAxioms 𝔸 B
  | nec {A}          : ofAxioms 𝔸 A → ofAxioms 𝔸 (□A)
  | rule1 {A B C}    : ofAxioms 𝔸 (A 🡒 B) → ofAxioms 𝔸 (C ▷ A 🡒 C ▷ B)
  | rule2 {A B C}    : ofAxioms 𝔸 (A 🡒 B) → ofAxioms 𝔸 (B ▷ C 🡒 A ▷ C)
  | verum            : ofAxioms 𝔸 Axioms.Verum
  | implyK {A B}     : ofAxioms 𝔸 (Axioms.ImplyK A B)
  | implyS {A B C}   : ofAxioms 𝔸 (Axioms.ImplyS A B C)
  | andElimL {A B}   : ofAxioms 𝔸 (Axioms.AndElim₁ A B)
  | andElimR {A B}   : ofAxioms 𝔸 (Axioms.AndElim₂ A B)
  | andIntro {A B}   : ofAxioms 𝔸 (Axioms.AndInst A B)
  | orIntroL {A B}   : ofAxioms 𝔸 (Axioms.OrInst₁ A B)
  | orIntroR {A B}   : ofAxioms 𝔸 (Axioms.OrInst₂ A B)
  | orElim {A B C}   : ofAxioms 𝔸 (Axioms.OrElim A B C)
  | dne {A}          : ofAxioms 𝔸 (Axioms.DNE A)
  | axiomK {A B}     : ofAxioms 𝔸 (□(A 🡒 B) 🡒 □A 🡒 □B)
  | axiomL {A}       : ofAxioms 𝔸 (□(□A 🡒 A) 🡒 □A)
  | axiomJ3 {A B C}  : ofAxioms 𝔸 (Axioms.J3 A B C)
  | axiomJ6 {A}      : ofAxioms 𝔸 (Axioms.J6 A)

namespace Logic.ofAxioms

variable {𝔸 𝔹 : Set (Formula α)}

instance : ModusPonens (ofAxioms 𝔸) := ⟨mdp⟩
instance : HasAxiomImplyK (ofAxioms 𝔸) := ⟨implyK⟩
instance : HasAxiomImplyS (ofAxioms 𝔸) := ⟨implyS⟩
instance : HasAxiomAndInst (ofAxioms 𝔸) := ⟨andIntro⟩

instance : Entailment.Minimal (ofAxioms 𝔸) where
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

instance : Entailment.Cl (ofAxioms 𝔸) where
  dne := dne

variable {A B C : Formula α}

lemma of_mem (h : A ∈ 𝔸) : ofAxioms 𝔸 ⊢ A := axm h

lemma box_mono (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ □A 🡒 □B := axiomK ⨀ nec h

lemma rhd_mono_right (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ C ▷ A 🡒 C ▷ B := rule1 h

lemma rhd_anti_left (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := rule2 h

/-- `ofAxioms 𝔸` is contained in every extension of $\mathbf{IL}^-$ that proves `𝔸`. -/
lemma subset_of_provable (h : ∀ A ∈ 𝔸, ofAxioms 𝔹 ⊢ A) : ofAxioms 𝔸 ⊆ ofAxioms 𝔹 := by
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

lemma subset_of_subset (h : 𝔸 ⊆ 𝔹) : ofAxioms 𝔸 ⊆ ofAxioms 𝔹 :=
  subset_of_provable fun _ hA ↦ axm (h hA)

end Logic.ofAxioms

end FFL.InterpretabilityLogic

end
