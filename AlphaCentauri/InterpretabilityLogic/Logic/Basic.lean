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

abbrev Logic (α : Type*) := Set (Formula α)

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

variable {L : Logic α} [L.ExtendsGL] {X : Set (Formula α)} {A B : Formula α}

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
lemma box_of_provable {T : Set (Formula α)} (h : (T ∪ (□·) '' T) *⊢[L] A) :
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
inductive Logic.ofAxioms (𝔸 : Set (Formula α)) : Logic α
  | axm {A}          : A ∈ 𝔸 → ofAxioms 𝔸 A
  | mdp {A B}        : ofAxioms 𝔸 (A 🡒 B) → ofAxioms 𝔸 A → ofAxioms 𝔸 B
  | nec {A}          : ofAxioms 𝔸 A → ofAxioms 𝔸 (□A)
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
  | axiomJ1 {A B}    : ofAxioms 𝔸 (Axioms.J1 A B)
  | axiomJ2 {A B C}  : ofAxioms 𝔸 (Axioms.J2 A B C)
  | axiomJ3 {A B C}  : ofAxioms 𝔸 (Axioms.J3 A B C)
  | axiomJ4 {A B}    : ofAxioms 𝔸 (Axioms.J4 A B)
  | axiomJ5 {A}      : ofAxioms 𝔸 (Axioms.J5 A)

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

instance : (ofAxioms 𝔸).ExtendsGL := ⟨nec, axiomK, axiomL⟩

variable {A B C : Formula α}

lemma rhd_mono_right (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ C ▷ A 🡒 C ▷ B := by
  have h₁ : ofAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h;
  have h₂ : ofAxioms 𝔸 ⊢ C ▷ A ⋏ A ▷ B 🡒 C ▷ B := axiomJ2;
  cl_prover [h₁, h₂];

lemma rhd_anti_left (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have h₁ : ofAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h;
  have h₂ : ofAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h₁, h₂];

/-- `ofAxioms 𝔸` is contained in every extension of $\mathbf{IL}$ that proves `𝔸`. -/
lemma subset_of_provable (h : ∀ A ∈ 𝔸, ofAxioms 𝔹 ⊢ A) : ofAxioms 𝔸 ⊆ ofAxioms 𝔹 := by
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

lemma subset_of_subset (h : 𝔸 ⊆ 𝔹) : ofAxioms 𝔸 ⊆ ofAxioms 𝔹 :=
  subset_of_provable fun _ hA ↦ axm (h hA)

end Logic.ofAxioms

/-! ### Theorems of extensions of $\mathbf{IL}$ -/

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {A B : Formula α}

lemma rhd_of_provable (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h

lemma rhd_refl : ofAxioms 𝔸 ⊢ A ▷ A := rhd_of_provable C_id

lemma box_neg_of_rhd : ofAxioms 𝔸 ⊢ A ▷ B 🡒 □(∼B) 🡒 □(∼A) := by
  have h : ofAxioms 𝔸 ⊢ A ▷ B 🡒 ∼□(∼A) 🡒 ∼□(∼B) := axiomJ4;
  cl_prover [h];

/-- - [Vis90, §6.1.1] -/
lemma rhd_bot : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼A) := by
  have h₁ : ofAxioms 𝔸 ⊢ □(∼⊥) := provable_box verum;
  have h₂ : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼⊥) 🡒 □(∼A) := box_neg_of_rhd;
  cl_prover [h₁, h₂];

lemma or_dia_rhd : ofAxioms 𝔸 ⊢ (A ⋎ ◇A) ▷ A := by
  have h₁ : ofAxioms 𝔸 ⊢ A ▷ A := rhd_refl;
  have h₂ : ofAxioms 𝔸 ⊢ ◇A ▷ A := axiomJ5;
  have h₃ : ofAxioms 𝔸 ⊢ A ▷ A ⋏ ◇A ▷ A 🡒 (A ⋎ ◇A) ▷ A := axiomJ3;
  cl_prover [h₁, h₂, h₃];

/-- - [Vis90, §6.1.1] -/
lemma rhd_and_box_neg : ofAxioms 𝔸 ⊢ A ▷ (A ⋏ □(∼A)) := by
  have h₁ : ofAxioms 𝔸 ⊢ □(□(∼A) 🡒 ∼A) 🡒 □(∼A) := axiomL;
  have h₂ : ofAxioms 𝔸 ⊢ □(∼(A ⋏ □(∼A))) 🡒 □(□(∼A) 🡒 ∼A) := box_mono <| by cl_prover;
  have h₃ : ofAxioms 𝔸 ⊢ A ▷ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) :=
    axiomJ1 ⨀ provable_box
      (show ofAxioms 𝔸 ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ∼□(∼(A ⋏ □(∼A))) by cl_prover [h₁, h₂]);
  have h₄ : ofAxioms 𝔸 ⊢ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) := or_dia_rhd;
  have h₅ : ofAxioms 𝔸 ⊢
      A ▷ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ⋏ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) 🡒
        A ▷ (A ⋏ □(∼A)) :=
    axiomJ2;
  cl_prover [h₃, h₄, h₅];

variable [DecidableEq α] {X : Set (Formula α)} {F : Formula α}

lemma fdisj_rhd {𝒢 : Finset (Formula α)} (h : ∀ G ∈ 𝒢, X *⊢[ofAxioms 𝔸] G ▷ F) :
    X *⊢[ofAxioms 𝔸] 𝒢.disj ▷ F := by
  induction 𝒢 using Finset.induction_on with
  | empty => simpa using Context.of (axiomJ1 ⨀ provable_box efq);
  | insert G 𝒢 _ ih =>
    have h₁ : X *⊢[ofAxioms 𝔸] (G ⋎ 𝒢.disj) ▷ F :=
      Context.of axiomJ3 ⨀ K_intro (h G (by simp)) (ih fun H hH ↦ h H (by simp [hH]));
    exact Context.of (rhd_anti_left CinsertFDisjAFDisj) ⨀ h₁;

end Logic.ofAxioms

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

end FFL.InterpretabilityLogic

end
