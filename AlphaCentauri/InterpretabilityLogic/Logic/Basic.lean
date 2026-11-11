module

public import AlphaCentauri.InterpretabilityLogic.Formula
public import Foundation.Propositional.Entailment.Cl
public import Foundation.Meta.ClProver

/-!
# Interpretability logics

A logic is a set of formulas, regarded as an `Entailment` via membership. The framework here is the
class of logics containing $\mathbf{GL}$, the axiom schemata of interpretability logic, the
extensions of $\mathbf{IL}$ by sets of axioms, and the theorems common to all of them. The
individual logics are in `Logic/<logic>/Basic.lean`.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

abbrev Logic (α : Type*) := FormulaSet α

open Entailment Formula

variable {α : Type*}

instance : Entailment (Logic α) (Formula α) := ⟨fun L A ↦ A ∈ L⟩

namespace Logic

variable {L L₁ L₂ : Logic α} {A : Formula α}

lemma weakerThan_iff : L₁ ⪯ L₂ ↔ L₁ ⊆ L₂ := ⟨fun h ↦ h.subset, fun h ↦ ⟨h⟩⟩

lemma strictlyWeakerThan_iff : L₁ ⪱ L₂ ↔ L₁ ⊂ L₂ :=
  ⟨fun h ↦ ⟨weakerThan_iff.mp h.weakerThan, fun h' ↦ h.notWT (weakerThan_iff.mpr h')⟩,
    fun h ↦ ⟨weakerThan_iff.mpr h.1, fun h' ↦ h.2 (weakerThan_iff.mp h')⟩⟩

lemma equiv_iff : L₁ ≊ L₂ ↔ L₁ = L₂ := ⟨fun h ↦ h.eq, fun h ↦ ⟨congrArg theory h⟩⟩

end Logic

/-! ### Logics containing $\mathbf{GL}$ -/

/-- `L` is closed under necessitation and proves the axioms $\mathbf{K}$ and $\mathbf{L}$. -/
class Logic.ExtendsGL (L : Logic α) : Prop where
  nec {A : Formula α} : L ⊢ A → L ⊢ □A
  axiomK {A B : Formula α} : L ⊢ □(A 🡒 B) 🡒 □A 🡒 □B
  axiomL {A : Formula α} : L ⊢ □(□A 🡒 A) 🡒 □A

namespace Logic

variable {L : Logic α} [L.ExtendsGL] {X : FormulaSet α} {A B : Formula α}

lemma provable_box (h : L ⊢ A) : L ⊢ □A := ExtendsGL.nec h

variable [Entailment.Cl L]

lemma box_mono (h : L ⊢ A 🡒 B) : L ⊢ □A 🡒 □B := ExtendsGL.axiomK ⨀ provable_box h

lemma box_and : L ⊢ □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : L ⊢ □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : L ⊢ □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := ExtendsGL.axiomK;
  cl_prover [h₁, h₂];

lemma axiom4 : L ⊢ □A 🡒 □□A := by
  have h₁ : L ⊢ □(□A ⋏ A) 🡒 □A := box_mono and₂;
  have h₂ : L ⊢ □A 🡒 □(□(□A ⋏ A) 🡒 □A ⋏ A) := box_mono <| by cl_prover [h₁];
  have h₃ : L ⊢ □(□(□A ⋏ A) 🡒 □A ⋏ A) 🡒 □(□A ⋏ A) := ExtendsGL.axiomL;
  have h₄ : L ⊢ □(□A ⋏ A) 🡒 □□A := box_mono and₁;
  cl_prover [h₂, h₃, h₄];

lemma box_conj_of_forall :
    (Δ : List (Formula α)) → (∀ B ∈ Δ, X *⊢[L] □B) → X *⊢[L] □Δ.conj
  | [], _ => Context.of <| provable_box verum
  | B :: Δ, h =>
    Context.of box_and ⨀
      K_intro (h B (by simp)) (box_conj_of_forall Δ fun C hC ↦ h C (by simp [hC]))

/-- If `A` follows from `T` together with the formulas `□B` for `B ∈ T`, then `□A` follows from the
latter. -/
lemma box_of_provable {T : FormulaSet α} (h : (T ∪ (□·) '' T) *⊢[L] A) :
    ((□·) '' T) *⊢[L] □A := by
  obtain ⟨Δ, hΔ, hb⟩ := Context.provable_iff.mp h;
  have h₁ : L ⊢ □Δ.conj 🡒 □A :=
    box_mono <| C_trans (K_right EConj₂Conj) (FiniteContext.provable_iff.mp hb);
  apply Context.of h₁ ⨀ box_conj_of_forall Δ _;
  intro B hB;
  rcases hΔ B hB with hB | ⟨C, hC, rfl⟩;
  · exact Context.by_axm ⟨B, hB, rfl⟩;
  · exact Context.of axiom4 ⨀ Context.by_axm ⟨C, hC, rfl⟩;

end Logic

/-! ### Axioms of $\mathbf{IL}$ -/

namespace Axioms

variable (A B C : Formula α)

/-- - [Vis90, §6.1] -/
protected abbrev J1 : Formula α := □(A 🡒 B) 🡒 A ▷ B

/-- - [Vis90, §6.1] -/
protected abbrev J2 : Formula α := A ▷ B ⋏ B ▷ C 🡒 A ▷ C

/-- - [Vis90, §6.1] -/
protected abbrev J3 : Formula α := A ▷ C ⋏ B ▷ C 🡒 (A ⋎ B) ▷ C

/-- - [Vis90, §6.1] -/
protected abbrev J4 : Formula α := A ▷ B 🡒 ◇A 🡒 ◇B

/-- - [Vis90, §6.1] -/
protected abbrev J5 : Formula α := ◇A ▷ A

end Axioms

/-! ### Extensions of $\mathbf{IL}$ -/

/-- The smallest logic containing `𝔸` and the axioms of $\mathbf{IL}$, closed under modus ponens
and necessitation.

- [Vis90, §6.1]
-/
inductive Logic.ofILAxioms (𝔸 : FormulaSet α) : Logic α
  | axm {A}          : A ∈ 𝔸 → ofILAxioms 𝔸 A
  | mdp {A B}        : ofILAxioms 𝔸 (A 🡒 B) → ofILAxioms 𝔸 A → ofILAxioms 𝔸 B
  | nec {A}          : ofILAxioms 𝔸 A → ofILAxioms 𝔸 (□A)
  | verum            : ofILAxioms 𝔸 Axioms.Verum
  | implyK {A B}     : ofILAxioms 𝔸 (Axioms.ImplyK A B)
  | implyS {A B C}   : ofILAxioms 𝔸 (Axioms.ImplyS A B C)
  | andElimL {A B}   : ofILAxioms 𝔸 (Axioms.AndElim₁ A B)
  | andElimR {A B}   : ofILAxioms 𝔸 (Axioms.AndElim₂ A B)
  | andIntro {A B}   : ofILAxioms 𝔸 (Axioms.AndInst A B)
  | orIntroL {A B}   : ofILAxioms 𝔸 (Axioms.OrInst₁ A B)
  | orIntroR {A B}   : ofILAxioms 𝔸 (Axioms.OrInst₂ A B)
  | orElim {A B C}   : ofILAxioms 𝔸 (Axioms.OrElim A B C)
  | dne {A}          : ofILAxioms 𝔸 (Axioms.DNE A)
  | axiomK {A B}     : ofILAxioms 𝔸 (□(A 🡒 B) 🡒 □A 🡒 □B)
  | axiomL {A}       : ofILAxioms 𝔸 (□(□A 🡒 A) 🡒 □A)
  | axiomJ1 {A B}    : ofILAxioms 𝔸 (Axioms.J1 A B)
  | axiomJ2 {A B C}  : ofILAxioms 𝔸 (Axioms.J2 A B C)
  | axiomJ3 {A B C}  : ofILAxioms 𝔸 (Axioms.J3 A B C)
  | axiomJ4 {A B}    : ofILAxioms 𝔸 (Axioms.J4 A B)
  | axiomJ5 {A}      : ofILAxioms 𝔸 (Axioms.J5 A)

namespace Logic.ofILAxioms

variable {𝔸 𝔹 : FormulaSet α}

instance : ModusPonens (ofILAxioms 𝔸) := ⟨mdp⟩
instance : HasAxiomImplyK (ofILAxioms 𝔸) := ⟨implyK⟩
instance : HasAxiomImplyS (ofILAxioms 𝔸) := ⟨implyS⟩
instance : HasAxiomAndInst (ofILAxioms 𝔸) := ⟨andIntro⟩

instance : Entailment.Minimal (ofILAxioms 𝔸) where
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

instance : Entailment.Cl (ofILAxioms 𝔸) where
  dne := dne

instance : (ofILAxioms 𝔸).ExtendsGL := ⟨nec, axiomK, axiomL⟩

variable {A B C : Formula α}

lemma rhd_mono_right (h : ofILAxioms 𝔸 ⊢ A 🡒 B) : ofILAxioms 𝔸 ⊢ C ▷ A 🡒 C ▷ B := by
  have h₁ : ofILAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h;
  have h₂ : ofILAxioms 𝔸 ⊢ C ▷ A ⋏ A ▷ B 🡒 C ▷ B := axiomJ2;
  cl_prover [h₁, h₂];

lemma rhd_anti_left (h : ofILAxioms 𝔸 ⊢ A 🡒 B) : ofILAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have h₁ : ofILAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h;
  have h₂ : ofILAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h₁, h₂];

/-- `ofILAxioms 𝔸` is contained in every extension of $\mathbf{IL}$ that proves `𝔸`. -/
lemma subset_of_provable (h : ∀ A ∈ 𝔸, ofILAxioms 𝔹 ⊢ A) : ofILAxioms 𝔸 ⊆ ofILAxioms 𝔹 := by
  intro A hA;
  induction hA with
  | axm hA => exact h _ hA;
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
  | nec _ ih => exact nec ih;
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
  | axiomJ1 => exact axiomJ1;
  | axiomJ2 => exact axiomJ2;
  | axiomJ3 => exact axiomJ3;
  | axiomJ4 => exact axiomJ4;
  | axiomJ5 => exact axiomJ5;

lemma subset_of_subset (h : 𝔸 ⊆ 𝔹) : ofILAxioms 𝔸 ⊆ ofILAxioms 𝔹 :=
  subset_of_provable fun _ hA ↦ axm (h hA)

end Logic.ofILAxioms

/-! ### Theorems of extensions of $\mathbf{IL}$ -/

namespace Logic.ofILAxioms

variable {𝔸 : FormulaSet α} {A B : Formula α}

lemma rhd_of_provable (h : ofILAxioms 𝔸 ⊢ A 🡒 B) : ofILAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h

lemma rhd_refl : ofILAxioms 𝔸 ⊢ A ▷ A := rhd_of_provable C_id

lemma box_neg_of_rhd : ofILAxioms 𝔸 ⊢ A ▷ B 🡒 □(∼B) 🡒 □(∼A) := by
  have h : ofILAxioms 𝔸 ⊢ A ▷ B 🡒 ∼□(∼A) 🡒 ∼□(∼B) := axiomJ4;
  cl_prover [h];

/-- - [Vis90, §6.1.1] -/
lemma rhd_bot : ofILAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼A) := by
  have h₁ : ofILAxioms 𝔸 ⊢ □(∼⊥) := provable_box verum;
  have h₂ : ofILAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼⊥) 🡒 □(∼A) := box_neg_of_rhd;
  cl_prover [h₁, h₂];

lemma or_dia_rhd : ofILAxioms 𝔸 ⊢ (A ⋎ ◇A) ▷ A := by
  have h₁ : ofILAxioms 𝔸 ⊢ A ▷ A := rhd_refl;
  have h₂ : ofILAxioms 𝔸 ⊢ ◇A ▷ A := axiomJ5;
  have h₃ : ofILAxioms 𝔸 ⊢ A ▷ A ⋏ ◇A ▷ A 🡒 (A ⋎ ◇A) ▷ A := axiomJ3;
  cl_prover [h₁, h₂, h₃];

/-- - [Vis90, §6.1.1] -/
lemma rhd_and_box_neg : ofILAxioms 𝔸 ⊢ A ▷ (A ⋏ □(∼A)) := by
  have h₁ : ofILAxioms 𝔸 ⊢ □(□(∼A) 🡒 ∼A) 🡒 □(∼A) := axiomL;
  have h₂ : ofILAxioms 𝔸 ⊢ □(∼(A ⋏ □(∼A))) 🡒 □(□(∼A) 🡒 ∼A) := box_mono <| by cl_prover;
  have h₃ : ofILAxioms 𝔸 ⊢ A ▷ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) :=
    axiomJ1 ⨀ provable_box
      (show ofILAxioms 𝔸 ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ∼□(∼(A ⋏ □(∼A))) by cl_prover [h₁, h₂]);
  have h₄ : ofILAxioms 𝔸 ⊢ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) := or_dia_rhd;
  have h₅ : ofILAxioms 𝔸 ⊢
      A ▷ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ⋏ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) 🡒
        A ▷ (A ⋏ □(∼A)) :=
    axiomJ2;
  cl_prover [h₃, h₄, h₅];

variable [DecidableEq α] {X : FormulaSet α} {F : Formula α}

lemma fdisj_rhd {𝒢 : Finset (Formula α)} (h : ∀ G ∈ 𝒢, X *⊢[ofILAxioms 𝔸] G ▷ F) :
    X *⊢[ofILAxioms 𝔸] 𝒢.disj ▷ F := by
  induction 𝒢 using Finset.induction_on with
  | empty => simpa using Context.of (axiomJ1 ⨀ provable_box efq);
  | insert G 𝒢 _ ih =>
    have h₁ : X *⊢[ofILAxioms 𝔸] (G ⋎ 𝒢.disj) ▷ F :=
      Context.of axiomJ3 ⨀ K_intro (h G (by simp)) (ih fun H hH ↦ h H (by simp [hH]));
    exact Context.of (rhd_anti_left CinsertFDisjAFDisj) ⨀ h₁;

end Logic.ofILAxioms

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

namespace Logic.ofILAxioms

variable {𝔸 : FormulaSet α} {A B C : Formula α}

lemma rhd_and_not_rhd_neg : ofILAxioms 𝔸 ⊢ A ▷ B ⋏ ∼(A ▷ ∼C) 🡒 ◇(B ⋏ □C) := by
  have h₀ : ofILAxioms 𝔸 ⊢ □(∼∼C) 🡒 □C := box_mono dne;
  have h₁ : ofILAxioms 𝔸 ⊢ ∼(B ⋏ □C) 🡒 B 🡒 ∼□(∼∼C) := by cl_prover [h₀];
  have h₂ : ofILAxioms 𝔸 ⊢ □(B 🡒 ∼□(∼∼C)) 🡒 B ▷ ◇(∼C) := axiomJ1;
  have h₃ : ofILAxioms 𝔸 ⊢ ◇(∼C) ▷ ∼C := axiomJ5;
  have h₄ : ofILAxioms 𝔸 ⊢ Axioms.J2 B (◇(∼C)) (∼C) := axiomJ2;
  have h₅ : ofILAxioms 𝔸 ⊢ Axioms.J2 A B (∼C) := axiomJ2;
  have : ofILAxioms 𝔸 ⊢ A ▷ B ⋏ ∼(A ▷ ∼C) 🡒 ∼□(∼(B ⋏ □C)) := by
    cl_prover [box_mono h₁, h₂, h₃, h₄, h₅];
  exact this;

end Logic.ofILAxioms



/-! ### Axioms of $\mathbf{CL}$ -/

namespace Axioms

variable (A B C : Formula α)

/-- - [KO21, §3.3] -/
protected abbrev J2Plus : Formula α := A ▷ (B ⋎ C) ⋏ B ▷ C 🡒 A ▷ C

/-- - [KO21, Definition 2.1] -/
protected abbrev J6 : Formula α := □A 🡘 ∼A ▷ ⊥

end Axioms

/-! ### Extensions of $\mathbf{CL}$ -/

/-- The smallest logic containing `𝔸` and the axioms of $\mathbf{CL}$, closed under modus ponens
and necessitation.

- [Ign91, Definition 2.2]
- [KO21, §3.5]
-/
inductive Logic.ofCLAxioms (𝔸 : FormulaSet α) : Logic α
  | axm {A}          : A ∈ 𝔸 → ofCLAxioms 𝔸 A
  | mdp {A B}        : ofCLAxioms 𝔸 (A 🡒 B) → ofCLAxioms 𝔸 A → ofCLAxioms 𝔸 B
  | nec {A}          : ofCLAxioms 𝔸 A → ofCLAxioms 𝔸 (□A)
  | verum            : ofCLAxioms 𝔸 Axioms.Verum
  | implyK {A B}     : ofCLAxioms 𝔸 (Axioms.ImplyK A B)
  | implyS {A B C}   : ofCLAxioms 𝔸 (Axioms.ImplyS A B C)
  | andElimL {A B}   : ofCLAxioms 𝔸 (Axioms.AndElim₁ A B)
  | andElimR {A B}   : ofCLAxioms 𝔸 (Axioms.AndElim₂ A B)
  | andIntro {A B}   : ofCLAxioms 𝔸 (Axioms.AndInst A B)
  | orIntroL {A B}   : ofCLAxioms 𝔸 (Axioms.OrInst₁ A B)
  | orIntroR {A B}   : ofCLAxioms 𝔸 (Axioms.OrInst₂ A B)
  | orElim {A B C}   : ofCLAxioms 𝔸 (Axioms.OrElim A B C)
  | dne {A}          : ofCLAxioms 𝔸 (Axioms.DNE A)
  | axiomK {A B}     : ofCLAxioms 𝔸 (□(A 🡒 B) 🡒 □A 🡒 □B)
  | axiomL {A}       : ofCLAxioms 𝔸 (□(□A 🡒 A) 🡒 □A)
  | axiomJ1 {A B}    : ofCLAxioms 𝔸 (Axioms.J1 A B)
  | axiomJ2 {A B C}  : ofCLAxioms 𝔸 (Axioms.J2 A B C)
  | axiomJ3 {A B C}  : ofCLAxioms 𝔸 (Axioms.J3 A B C)
  | axiomJ4 {A B}    : ofCLAxioms 𝔸 (Axioms.J4 A B)

namespace Logic.ofCLAxioms

variable {𝔸 𝔹 : FormulaSet α}

instance : ModusPonens (ofCLAxioms 𝔸) := ⟨mdp⟩
instance : HasAxiomImplyK (ofCLAxioms 𝔸) := ⟨implyK⟩
instance : HasAxiomImplyS (ofCLAxioms 𝔸) := ⟨implyS⟩
instance : HasAxiomAndInst (ofCLAxioms 𝔸) := ⟨andIntro⟩

instance : Entailment.Minimal (ofCLAxioms 𝔸) where
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

instance : Entailment.Cl (ofCLAxioms 𝔸) where
  dne := dne

instance : (ofCLAxioms 𝔸).ExtendsGL := ⟨nec, axiomK, axiomL⟩

/-- `ofCLAxioms 𝔸` is contained in every extension of $\mathbf{CL}$ that proves `𝔸`. -/
lemma subset_of_provable (h : ∀ A ∈ 𝔸, ofCLAxioms 𝔹 ⊢ A) :
    ofCLAxioms 𝔸 ⊆ ofCLAxioms 𝔹 := by
  intro A hA;
  induction hA with
  | axm hA => exact h _ hA;
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA;
  | nec _ ih => exact nec ih;
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
  | axiomJ1 => exact axiomJ1;
  | axiomJ2 => exact axiomJ2;
  | axiomJ3 => exact axiomJ3;
  | axiomJ4 => exact axiomJ4;

lemma subset_of_subset (h : 𝔸 ⊆ 𝔹) : ofCLAxioms 𝔸 ⊆ ofCLAxioms 𝔹 :=
  subset_of_provable fun _ hA ↦ axm (h hA)

variable {A B C : Formula α}

/-- - [KO21, Proposition 3.20.2] -/
lemma rhd_mono_right (h : ofCLAxioms 𝔸 ⊢ A 🡒 B) : ofCLAxioms 𝔸 ⊢ C ▷ A 🡒 C ▷ B := by
  have h₁ : ofCLAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h;
  have h₂ : ofCLAxioms 𝔸 ⊢ C ▷ A ⋏ A ▷ B 🡒 C ▷ B := axiomJ2;
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 3.20.3] -/
lemma rhd_anti_left (h : ofCLAxioms 𝔸 ⊢ A 🡒 B) : ofCLAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have h₁ : ofCLAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h;
  have h₂ : ofCLAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 3.1] -/
lemma rhd_refl : ofCLAxioms 𝔸 ⊢ A ▷ A := axiomJ1 ⨀ provable_box C_id

/-- - [KO21, Proposition 3.20.1] -/
lemma axiomJ6 : ofCLAxioms 𝔸 ⊢ Axioms.J6 A := by
  have h₁ : ofCLAxioms 𝔸 ⊢ □A 🡒 □(∼A 🡒 ⊥) := box_mono (by cl_prover);
  have h₂ : ofCLAxioms 𝔸 ⊢ □(∼A 🡒 ⊥) 🡒 ∼A ▷ ⊥ := axiomJ1;
  have h₃ : ofCLAxioms 𝔸 ⊢ ∼A ▷ ⊥ 🡒 ∼□(∼∼A) 🡒 ∼□(∼⊥) := axiomJ4;
  have h₄ : ofCLAxioms 𝔸 ⊢ □(∼⊥) := provable_box (by cl_prover);
  have h₅ : ofCLAxioms 𝔸 ⊢ □(∼∼A) 🡒 □A := box_mono (by cl_prover);
  cl_prover [h₁, h₂, h₃, h₄, h₅];

lemma box_neg_iff_rhd_bot : ofCLAxioms 𝔸 ⊢ □(∼A) 🡘 A ▷ ⊥ := by
  have h₁ : ofCLAxioms 𝔸 ⊢ □(∼A) 🡘 ∼∼A ▷ ⊥ := axiomJ6;
  have h₂ : ofCLAxioms 𝔸 ⊢ ∼∼A ▷ ⊥ 🡒 A ▷ ⊥ := rhd_anti_left dni;
  have h₃ : ofCLAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 ∼∼A ▷ ⊥ := rhd_anti_left dne;
  cl_prover [h₁, h₂, h₃];

/-- - [KO21, Proposition 2.5.1] -/
lemma rhd_of_box_neg : ofCLAxioms 𝔸 ⊢ □(∼A) 🡒 A ▷ B := by
  have h₁ : ofCLAxioms 𝔸 ⊢ □(∼A) 🡘 A ▷ ⊥ := box_neg_iff_rhd_bot;
  have h₂ : ofCLAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 A ▷ B := rhd_mono_right efq;
  cl_prover [h₁, h₂];

/-- - [KO21, Proposition 2.5.2] -/
lemma rhd_anti_left_of_box : ofCLAxioms 𝔸 ⊢ □(A 🡒 B) 🡒 B ▷ C 🡒 A ▷ C := by
  have h₁ : ofCLAxioms 𝔸 ⊢ □(A 🡒 B) 🡒 □(∼(A ⋏ ∼B)) := box_mono (by cl_prover);
  have h₂ : ofCLAxioms 𝔸 ⊢ □(∼(A ⋏ ∼B)) 🡒 (A ⋏ ∼B) ▷ C := rhd_of_box_neg;
  have h₃ : ofCLAxioms 𝔸 ⊢ (A ⋏ ∼B) ▷ C ⋏ B ▷ C 🡒 (A ⋏ ∼B ⋎ B) ▷ C := axiomJ3;
  have h₄ : ofCLAxioms 𝔸 ⊢ (A ⋏ ∼B ⋎ B) ▷ C 🡒 A ▷ C := rhd_anti_left (by cl_prover);
  cl_prover [h₁, h₂, h₃, h₄];

/-- - [KO21, Proposition 3.12.2] -/
lemma axiomJ2Plus : ofCLAxioms 𝔸 ⊢ Axioms.J2Plus A B C := by
  have h₁ : ofCLAxioms 𝔸 ⊢ B ▷ C ⋏ C ▷ C 🡒 (B ⋎ C) ▷ C := axiomJ3;
  have h₂ : ofCLAxioms 𝔸 ⊢ C ▷ C := rhd_refl;
  have h₃ : ofCLAxioms 𝔸 ⊢ A ▷ (B ⋎ C) ⋏ (B ⋎ C) ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h₁, h₂, h₃]

lemma fdisj_rhd [DecidableEq α] {X : FormulaSet α} {𝒢 : Finset (Formula α)}
    (h : ∀ G ∈ 𝒢, X *⊢[ofCLAxioms 𝔸] G ▷ C) : X *⊢[ofCLAxioms 𝔸] 𝒢.disj ▷ C := by
  induction 𝒢 using Finset.induction_on with
  | empty => simpa using Context.of (rhd_of_box_neg (A := ⊥) (B := C) ⨀ provable_box verum);
  | insert G 𝒢 _ ih =>
    have h₁ : X *⊢[ofCLAxioms 𝔸] (G ⋎ 𝒢.disj) ▷ C :=
      Context.of axiomJ3 ⨀ K_intro (h G (by simp)) (ih fun H hH ↦ h H (by simp [hH]));
    exact Context.of (rhd_anti_left CinsertFDisjAFDisj) ⨀ h₁;

end Logic.ofCLAxioms

/-! ### Logics proving $\mathbf{J5}$ -/

class Logic.HasAxiomJ5 (L : Logic α) : Prop where
  J5 (A : Formula α) : L ⊢ Axioms.J5 A

instance : Logic.HasAxiomJ5 (Logic.ofCLAxioms {Axioms.J5 A | A} : Logic α) :=
  ⟨fun _ ↦ Logic.ofCLAxioms.axm ⟨_, rfl⟩⟩

end FFL.InterpretabilityLogic
