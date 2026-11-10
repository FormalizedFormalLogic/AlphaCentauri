module

public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Logic

/-!
# Sublogics of $\mathbf{IL}$ extending $\mathbf{IL}^-$

The logic $\mathbf{IL}^-$, its extensions by the schemata $\mathbf{J1}$, $\mathbf{J2}$,
$\mathbf{J2}^+$, $\mathbf{J4}$, $\mathbf{J4}^+$ and $\mathbf{J5}$, the principles derivable in
them, the inclusions between them, and $\mathbf{IL}$ as
$\mathbf{IL}^-(\mathbf{J1}, \mathbf{J2}, \mathbf{J5})$.
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

lemma box_mono (h : ofAxiomsMinus 𝔸 ⊢ A 🡒 B) : ofAxiomsMinus 𝔸 ⊢ □A 🡒 □B := axiomK ⨀ nec h

lemma rhd_mono_right (h : ofAxiomsMinus 𝔸 ⊢ A 🡒 B) : ofAxiomsMinus 𝔸 ⊢ C ▷ A 🡒 C ▷ B := rule1 h

lemma rhd_anti_left (h : ofAxiomsMinus 𝔸 ⊢ A 🡒 B) : ofAxiomsMinus 𝔸 ⊢ B ▷ C 🡒 A ▷ C := rule2 h

lemma rhd_self_of_J1 (h : ∀ A B, ofAxiomsMinus 𝔸 ⊢ Axioms.J1 A B) : ofAxiomsMinus 𝔸 ⊢ A ▷ A := by
  have : ofAxiomsMinus 𝔸 ⊢ A 🡒 A := C_id;
  exact h A A ⨀ nec this;

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

/-- $\mathbf{CL}$, presented as $\mathbf{IL}^-(\mathbf{J1}, \mathbf{J2})$.

- [KO21, Proposition 3.21]
-/
abbrev CL : Logic α :=
  ofAxiomsMinus ({Axioms.J1 A B | (A) (B)} ∪ {Axioms.J2 A B C | (A) (B) (C)})

notation "𝐂𝐋" => Logic.CL

end Logic

/-! ### Derived principles -/

namespace Logic

open ofAxiomsMinus

variable {A B C : Formula α}

namespace ILMinusJ1

@[simp] lemma axiomJ1 : ILMinusJ1 ⊢ Axioms.J1 A B := axm (by simp)

/-- - [KO21, Proposition 3.1] -/
@[simp] lemma axiomJ1' : ILMinusJ1 ⊢ Axioms.J1' A := rhd_self_of_J1 fun _ _ ↦ axiomJ1

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
  have h₂ : 𝐂𝐋 ⊢ C ▷ C := rhd_self_of_J1 fun _ _ ↦ axiomJ1;
  have h₃ : 𝐂𝐋 ⊢ A ▷ (B ⋎ C) ⋏ (B ⋎ C) ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h₁, h₂, h₃];

end CL

end Logic

end FFL.InterpretabilityLogic

end
