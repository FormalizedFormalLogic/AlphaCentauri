module

public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic
public import AlphaCentauri.ToFoundation.ProvabilityLogic.GL.LRClosure

/-!
# The logic $\mathbf{CLM}$

The extension of $\mathbf{CL}$ by the principle $\mathsf{M}$, and its soundness with respect to the
$\mathbf{CL}$-models satisfying the frame condition of $\mathsf{M}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-- - [Ign91, Definition 2.3] -/
abbrev Logic.CLM : Logic α := Logic.ofCLAxioms {Axioms.M A B C | (A) (B) (C)}

notation "𝐂𝐋𝐌" => Logic.CLM

namespace Logic

open ofCLAxioms

variable {A B C : Formula α}

@[simp] lemma CLM.axiomM : 𝐂𝐋𝐌 ⊢ Axioms.M A B C := axm ⟨A, B, C, rfl⟩

instance : (𝐂𝐋 : Logic α) ⪯ 𝐂𝐋𝐌 := weakerThan_iff.mpr <| subset_of_subset (Set.empty_subset _)

instance : (𝐂𝐋𝐌 : Logic α) ⪯ 𝐈𝐋𝐌 := by
  rw [weakerThan_iff, ILM, ofILAxioms.eq_ofCLAxioms];
  exact subset_of_subset Set.subset_union_right;

/-! ## Soundness -/

open Veltman Veltman.Model.World

/-- - [Ign91, Definition 3.3]
- [Ign91, Lemma 3.5]
-/
theorem CLM.sound {κ : Type*} [Nonempty κ] {M : Veltman.Model κ α} [M.IsCL] [M.HasM]
    (h : 𝐂𝐋𝐌 ⊢ A) : M ⊧ A :=
  ofCLAxioms.sound (by rintro _ ⟨A, B, C, rfl⟩ x; exact forces_axiomM) h

end Logic

/-! ## Modal formulas over formulas -/

namespace Formula

/-- The formula obtained from a modal formula whose atoms are formulas by reading each atom as
itself. -/
def ofModal : ProvabilityLogic.Formula (Formula α) → Formula α
  | .atom A => A
  | .falsum => ⊥
  | .imp A B => ofModal A 🡒 ofModal B
  | .box A => □(ofModal A)

@[simp] lemma ofModal_atom {A : Formula α} : ofModal (.atom A) = A := rfl
@[simp] lemma ofModal_falsum : ofModal (⊥ : ProvabilityLogic.Formula (Formula α)) = ⊥ := rfl
@[simp] lemma ofModal_imp {A B : ProvabilityLogic.Formula (Formula α)} :
    ofModal (A 🡒 B) = ofModal A 🡒 ofModal B := rfl
@[simp] lemma ofModal_box {A : ProvabilityLogic.Formula (Formula α)} :
    ofModal (□A) = □(ofModal A) := rfl

end Formula

namespace Logic

variable {L : Logic α} [L.ExtendsGL] [Entailment.Cl L]

lemma provable_ofModal {A : ProvabilityLogic.Formula (Formula α)} (h : 𝐆𝐋 ⊢ A) :
    L ⊢ Formula.ofModal A := by
  induction h with
  | axm h =>
    rcases h with ⟨B, rfl⟩ | ⟨B, rfl⟩
    · exact axiom4
    · exact ExtendsGL.axiomL
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | nec _ ih => exact provable_box ih
  | verum => exact verum
  | implyK => exact implyK
  | implyS => exact implyS
  | andElimL => exact and₁
  | andElimR => exact and₂
  | andIntro => exact and₃
  | orIntroL => exact or₁
  | orIntroR => exact or₂
  | orElim => exact or₃
  | dne => exact dne
  | axiomK => exact ExtendsGL.axiomK

end Logic

/-! ## Adequate sets for $\mathbf{CLM}$ -/

section

open ProvabilityLogic (LRClosure)
open ProvabilityLogic.LRClosure (IsBoxBody)

variable [DecidableEq α]

namespace clmAdequateClosure

variable (X : Finset (Formula α))

/-- The members of `X` and their negations. -/
noncomputable def atoms : Finset (Formula α) := X ∪ X.image (∼·)

/-- Representatives up to $\mathbf{GL}$-equivalence of the two parts of the LR-closure of
`atoms X`. -/
noncomputable def reps (b : Bool) : Finset (ProvabilityLogic.Formula (Formula α)) :=
  (LRClosure.finiteUpToEquiv (atoms X) b).exists_finset_subset.choose

open Classical in
/-- The antecedents and consequents of `▷`-formulas in `X`, and the representatives of the first
part of the LR-closure. -/
noncomputable def operands : Finset (Formula α) :=
  X.filter (IsRhdOperand X) ∪ (reps X true).image Formula.ofModal

open Classical in
/-- The `□`-formulas in `X`, and the formulas `□∼A` for the representatives `A` of the
LR-closure. -/
noncomputable def boxes : Finset (Formula α) :=
  X.filter (fun A ↦ ∃ B, A = □B) ∪
    (reps X true ∪ reps X false).image fun Z ↦ □(∼(Formula.ofModal Z))

/-- The formulas whose subformulas form `clmAdequateClosure X`. -/
noncomputable def generators : Finset (Formula α) :=
  X ∪ (operands X ×ˢ operands X).image (fun p ↦ p.1 ▷ p.2) ∪
    (operands X).image (fun A ↦ □(∼A)) ∪ boxes X ∪
    (operands X ×ˢ (operands X ∪ (operands X).image (◇·)).powerset).image
      (fun p ↦ □(p.1 🡒 p.2.disj))

/-- Every `▷`-subformula of `A` is in `X`, and every `□`-subformula of `A` is in `X` or the
translation of the body of a `□`-formula of the LR-closure of `atoms X`. -/
def Tame (A : Formula α) : Prop :=
  ∀ C ∈ A.subformulas, (∀ B D, C = B ▷ D → C ∈ X) ∧
    ∀ E, C = □E → C ∈ X ∨ ∃ E', IsBoxBody (atoms X) E' ∧ E = Formula.ofModal E'

variable {X} {b : Bool} {Z : ProvabilityLogic.Formula (Formula α)} {A B C : Formula α}

lemma lrClosure_of_mem_reps (h : Z ∈ reps X b) : LRClosure (atoms X) b Z :=
  (LRClosure.finiteUpToEquiv (atoms X) b).exists_finset_subset.choose_spec.1 h

lemma exists_mem_reps (h : LRClosure (atoms X) b Z) : ∃ Z' ∈ reps X b, 𝐆𝐋 ⊢ Z 🡘 Z' :=
  (LRClosure.finiteUpToEquiv (atoms X) b).exists_finset_subset.choose_spec.2 Z h

lemma mem_atoms_of_mem (h : A ∈ X) : A ∈ atoms X := Finset.mem_union_left _ h

lemma neg_mem_atoms_of_mem (h : A ∈ X) : ∼A ∈ atoms X :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

lemma exists_of_mem_operands (h : A ∈ operands X) :
    ∃ Z, LRClosure (atoms X) true Z ∧ Formula.ofModal Z = A := by
  classical
  rcases Finset.mem_union.mp h with h | h
  · exact ⟨.atom A, .atom (mem_atoms_of_mem (Finset.mem_filter.mp h).1), rfl⟩
  · obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp h
    exact ⟨Z, lrClosure_of_mem_reps hZ, rfl⟩

namespace Tame

lemma of_mem_subformulas (h : Tame X A) (hB : B ∈ A.subformulas) : Tame X B :=
  fun C hC ↦ h C (subformulas_subset_of_mem hB hC)

lemma falsum : Tame X ⊥ := by
  intro C hC
  simp only [subformulas, Finset.mem_singleton] at hC
  subst hC
  exact ⟨by simp, by simp⟩

lemma imp (hA : Tame X A) (hB : Tame X B) : Tame X (A 🡒 B) := by
  intro C hC
  simp only [subformulas, Finset.mem_insert, Finset.mem_union] at hC
  rcases hC with rfl | hC | hC
  · exact ⟨by simp, by simp⟩
  · exact hA C hC
  · exact hB C hC

lemma box (hA : Tame X A) (h : ∃ E', IsBoxBody (atoms X) E' ∧ A = Formula.ofModal E') :
    Tame X (□A) := by
  intro C hC
  simp only [subformulas, Finset.mem_insert] at hC
  rcases hC with rfl | hC
  · exact ⟨by simp, fun E hE ↦ .inr (by simpa [← box_inj.mp hE] using h)⟩
  · exact hA C hC

lemma disj₂ : {l : List (Formula α)} → (∀ A ∈ l, Tame X A) → Tame X (⋁l)
  | [], _ => falsum
  | [A], h => h A (by simp)
  | A :: B :: l, h =>
    imp (imp (h A (by simp)) falsum) (disj₂ (l := B :: l) fun C hC ↦ h C (by simp_all))

lemma disj {S : Finset (Formula α)} (h : ∀ A ∈ S, Tame X A) : Tame X S.disj :=
  disj₂ fun A hA ↦ h A (Finset.mem_toList.mp hA)

variable [Adequate X]

lemma of_mem (h : A ∈ X) : Tame X A := by
  intro C hC
  have hC := Adequate.subformulas_subset h hC
  exact ⟨fun _ _ _ ↦ hC, fun _ _ ↦ .inl hC⟩

lemma ofModal {W : ProvabilityLogic.Formula (Formula α)}
    (hatom : ∀ a, .atom a ∈ W.subfmls → a ∈ atoms X)
    (hbox : ∀ E, □E ∈ W.subfmls → IsBoxBody (atoms X) E) : Tame X (Formula.ofModal W) := by
  induction W with
  | atom a =>
    rcases Finset.mem_union.mp (hatom a (by simp)) with h | h
    · exact of_mem h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact imp (of_mem ha) falsum
  | falsum => exact falsum
  | imp V W ihV ihW =>
    exact imp (ihV (fun a h ↦ hatom a (by simp [ProvabilityLogic.Formula.subfmls, h]))
        fun E h ↦ hbox E (by simp [ProvabilityLogic.Formula.subfmls, h]))
      (ihW (fun a h ↦ hatom a (by simp [ProvabilityLogic.Formula.subfmls, h]))
        fun E h ↦ hbox E (by simp [ProvabilityLogic.Formula.subfmls, h]))
  | box W ih =>
    exact box (ih (fun a h ↦ hatom a (by simp [ProvabilityLogic.Formula.subfmls, h]))
        fun E h ↦ hbox E (by simp [ProvabilityLogic.Formula.subfmls, h]))
      ⟨W, hbox W (by simp [ProvabilityLogic.Formula.subfmls]), rfl⟩

lemma ofModal_of_lrClosure (h : LRClosure (atoms X) b Z) : Tame X (Formula.ofModal Z) :=
  ofModal (fun _ ha ↦ LRClosure.mem_of_atom_mem_subfmls h ha)
    fun _ hE ↦ LRClosure.isBoxBody_of_box_mem_subfmls h hE

lemma box_neg_ofModal (h : LRClosure (atoms X) b Z) : Tame X (□(∼Formula.ofModal Z)) :=
  box (imp (ofModal_of_lrClosure h) falsum) ⟨∼Z, .inl ⟨Z, b, h, rfl⟩, rfl⟩

lemma dia_ofModal (h : LRClosure (atoms X) true Z) : Tame X (◇Formula.ofModal Z) :=
  imp (box_neg_ofModal h) falsum

lemma of_mem_operands (h : A ∈ operands X) : Tame X A := by
  obtain ⟨Z, hZ, rfl⟩ := exists_of_mem_operands h
  exact ofModal_of_lrClosure hZ

end Tame

end clmAdequateClosure

end

end FFL.InterpretabilityLogic
