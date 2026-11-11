module

public import AlphaCentauri.InterpretabilityLogic.Logic.CL.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.ILM.Basic
public import AlphaCentauri.ToFoundation.ProvabilityLogic.GL.LRClosure

/-!
# The logic $\mathbf{CLM}$

The extension of $\mathbf{CL}$ by the principle $\mathsf{M}$, its soundness with respect to the
$\mathbf{CL}$-models satisfying the frame condition of $\mathsf{M}$, and its completeness with
respect to the finite ones. $\mathbf{CLM}$ lies strictly between $\mathbf{CL}$ and $\mathbf{ILM}$.

The countermodel lives on maximal consistent subsets of a $\mathbf{CLM}$-adequate set, a finite set
whose operands are closed up to $\mathbf{GL}$-equivalence under conjunction with `□`-formulas,
indexed by sequences of operands.

- [Ign91, §6]
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

open clmAdequateClosure in
/-- A finite set containing `X` whose operands are, up to $\mathbf{GL}$-equivalence, closed under
conjunction with `□`-formulas.

- [Ign91, Lemma 6.5]
-/
noncomputable def clmAdequateClosure (X : Finset (Formula α)) : Finset (Formula α) :=
  (generators X).biUnion subformulas

namespace clmAdequateClosure

variable {X : Finset (Formula α)} {A B C : Formula α}

lemma mem_iff : A ∈ clmAdequateClosure X ↔ ∃ g ∈ generators X, A ∈ g.subformulas :=
  Finset.mem_biUnion

lemma mem_of_mem_generators (h : A ∈ generators X) : A ∈ clmAdequateClosure X :=
  mem_iff.mpr ⟨A, h, mem_subformulas_self⟩

lemma subset : X ⊆ clmAdequateClosure X := fun _ h ↦
  mem_of_mem_generators <| Finset.mem_union_left _ <| Finset.mem_union_left _ <|
    Finset.mem_union_left _ <| Finset.mem_union_left _ h

lemma mem_of_mem_subformulas (hA : A ∈ clmAdequateClosure X) (hB : B ∈ A.subformulas) :
    B ∈ clmAdequateClosure X := by
  obtain ⟨g, hg, hA⟩ := mem_iff.mp hA
  exact mem_iff.mpr ⟨g, hg, subformulas_subset_of_mem hA hB⟩

lemma rhd_mem_of_mem_operands (hA : A ∈ operands X) (hB : B ∈ operands X) :
    A ▷ B ∈ clmAdequateClosure X :=
  mem_of_mem_generators <| Finset.mem_union_left _ <| Finset.mem_union_left _ <|
    Finset.mem_union_left _ <| Finset.mem_union_right _ <|
      Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩, rfl⟩

lemma box_neg_mem_of_mem_operands (hA : A ∈ operands X) : □(∼A) ∈ clmAdequateClosure X :=
  mem_of_mem_generators <| Finset.mem_union_left _ <| Finset.mem_union_left _ <|
    Finset.mem_union_right _ <| Finset.mem_image_of_mem _ hA

lemma mem_of_mem_boxes (h : A ∈ boxes X) : A ∈ clmAdequateClosure X :=
  mem_of_mem_generators <| Finset.mem_union_left _ <| Finset.mem_union_right _ h

lemma box_imp_disj_mem_of_mem_operands {S : Finset (Formula α)} (hB : B ∈ operands X)
    (hS : S ⊆ operands X ∪ (operands X).image (◇·)) :
    □(B 🡒 S.disj) ∈ clmAdequateClosure X :=
  mem_of_mem_generators <| Finset.mem_union_right _ <|
    Finset.mem_image.mpr ⟨(B, S), Finset.mem_product.mpr ⟨hB, Finset.mem_powerset.mpr hS⟩, rfl⟩

variable [Adequate X]

/-- The members of `clmAdequateClosure X` are tame, `▷`-formulas of operands, or `□`-formulas
`□(B 🡒 ⋁S)` of an operand `B` and operands or their `◇`-formulas `S`. -/
lemma tame_or_of_mem (h : A ∈ clmAdequateClosure X) :
    Tame X A ∨ (∃ B ∈ operands X, ∃ C ∈ operands X, A = B ▷ C) ∨
      ∃ B ∈ operands X, ∃ S ⊆ operands X ∪ (operands X).image (◇·), A = □(B 🡒 S.disj) := by
  classical
  obtain ⟨g, hg, hA⟩ := mem_iff.mp h
  simp only [generators, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists,
    Finset.mem_powerset] at hg
  rcases hg with ((((hg | ⟨B, C, ⟨hB, hC⟩, rfl⟩) | ⟨B, hB, rfl⟩) | hg) | ⟨B, S, ⟨hB, hS⟩, rfl⟩)
  · exact .inl <| (Tame.of_mem hg).of_mem_subformulas hA
  · simp only [subformulas, Finset.mem_insert, Finset.mem_union] at hA
    rcases hA with rfl | hA | hA
    · exact .inr <| .inl ⟨B, hB, C, hC, rfl⟩
    · exact .inl <| (Tame.of_mem_operands hB).of_mem_subformulas hA
    · exact .inl <| (Tame.of_mem_operands hC).of_mem_subformulas hA
  · obtain ⟨Z, hZ, rfl⟩ := exists_of_mem_operands hB
    exact .inl <| (Tame.box_neg_ofModal hZ).of_mem_subformulas hA
  · rcases Finset.mem_union.mp hg with hg | hg
    · exact .inl <| (Tame.of_mem (Finset.mem_filter.mp hg).1).of_mem_subformulas hA
    · obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hg
      rcases Finset.mem_union.mp hZ with hZ | hZ
      · exact .inl <| (Tame.box_neg_ofModal (lrClosure_of_mem_reps hZ)).of_mem_subformulas hA
      · exact .inl <| (Tame.box_neg_ofModal (lrClosure_of_mem_reps hZ)).of_mem_subformulas hA
  · rcases Finset.mem_insert.mp hA with rfl | hA
    · exact .inr <| .inr ⟨B, hB, S, hS, rfl⟩
    refine .inl <| Tame.of_mem_subformulas
      (Tame.imp (Tame.of_mem_operands hB) (Tame.disj fun C hC ↦ ?_)) hA
    rcases Finset.mem_union.mp (hS hC) with hC | hC
    · exact Tame.of_mem_operands hC
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨Z, hZ, rfl⟩ := exists_of_mem_operands hD
      exact Tame.dia_ofModal hZ

lemma mem_operands_of_rhd_mem (h : A ▷ B ∈ clmAdequateClosure X) :
    A ∈ operands X ∧ B ∈ operands X := by
  classical
  rcases tame_or_of_mem h with h | ⟨A', hA, B', hB, h⟩ | ⟨_, _, _, _, h⟩
  · have h := (h _ mem_subformulas_self).1 A B rfl
    exact ⟨Finset.mem_union_left _ <| Finset.mem_filter.mpr ⟨Adequate.rhd_left h, .of_rhd_left h⟩,
      Finset.mem_union_left _ <| Finset.mem_filter.mpr ⟨Adequate.rhd_right h, .of_rhd_right h⟩⟩
  · obtain ⟨rfl, rfl⟩ := rhd_inj.mp h
    exact ⟨hA, hB⟩
  · simp at h

lemma mem_operands_iff : IsRhdOperand (clmAdequateClosure X) A ↔ A ∈ operands X := by
  constructor
  · rintro ⟨B, h | h⟩
    · exact (mem_operands_of_rhd_mem h).1
    · exact (mem_operands_of_rhd_mem h).2
  · intro h
    exact .of_rhd_left (rhd_mem_of_mem_operands h h)

instance : CLAdequate (clmAdequateClosure X) where
  imp_left h := mem_of_mem_subformulas h (by simp [subformulas])
  imp_right h := mem_of_mem_subformulas h (by simp [subformulas])
  box h := mem_of_mem_subformulas h (by simp [subformulas])
  rhd_left h := mem_of_mem_subformulas h (by simp [subformulas])
  rhd_right h := mem_of_mem_subformulas h (by simp [subformulas])
  bot_rhd_bot := subset Adequate.bot_rhd_bot
  rhd_mem hA hB := rhd_mem_of_mem_operands (mem_operands_iff.mp hA) (mem_operands_iff.mp hB)
  box_neg_mem hA := box_neg_mem_of_mem_operands (mem_operands_iff.mp hA)
  box_imp_disj_mem {B S} hB hS := by
    refine box_imp_disj_mem_of_mem_operands (mem_operands_iff.mp hB) fun C hC ↦ ?_
    rcases hS C hC with hC | ⟨G, hG, rfl⟩
    · exact Finset.mem_union_left _ (mem_operands_iff.mp hC)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_operands_iff.mp hG))

/-! ### Representatives of conjunctions with `□`-formulas -/

open Entailment

variable {L : Logic α} [L.ExtendsGL] [Entailment.Cl L]

omit [DecidableEq α] [Adequate X] in
lemma ofModal_disj₂ : (l : List (ProvabilityLogic.Formula (Formula α))) →
    Formula.ofModal (⋁l) = ⋁(l.map Formula.ofModal)
  | [] => rfl
  | [_] => rfl
  | A :: B :: l => by
    change Formula.ofModal A ⋎ Formula.ofModal (⋁(B :: l)) = _
    rw [ofModal_disj₂ (B :: l)]
    rfl

omit [Adequate X] [L.ExtendsGL] in
lemma ofModal_disj_imp {U : Finset (ProvabilityLogic.Formula (Formula α))} {D : Formula α}
    (h : ∀ Z ∈ U, L ⊢ Formula.ofModal Z 🡒 D) : L ⊢ Formula.ofModal U.disj 🡒 D := by
  change L ⊢ Formula.ofModal (⋁U.toList) 🡒 D
  rw [ofModal_disj₂]
  apply left_Disj₂_intro
  intro C hC
  obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hC
  exact h Z (Finset.mem_toList.mp hZ)

omit [Adequate X] [L.ExtendsGL] in
lemma imp_ofModal_disj {U : Finset (ProvabilityLogic.Formula (Formula α))}
    {Z : ProvabilityLogic.Formula (Formula α)} (h : Z ∈ U) :
    L ⊢ Formula.ofModal Z 🡒 Formula.ofModal U.disj := by
  change L ⊢ Formula.ofModal Z 🡒 Formula.ofModal (⋁U.toList)
  rw [ofModal_disj₂]
  exact right_Disj₂_intro _ (List.mem_map_of_mem (Finset.mem_toList.mpr h))

/-- Every `□`-formula in `clmAdequateClosure X` is equivalent to the translation of a `□`-formula
of the LR-closure of `atoms X`. -/
lemma exists_isBoxBody_of_box_mem {E : Formula α} (h : □E ∈ clmAdequateClosure X) :
    ∃ E', IsBoxBody (atoms X) E' ∧ L ⊢ □E 🡘 □(Formula.ofModal E') := by
  classical
  rcases tame_or_of_mem h with h | ⟨_, _, _, _, h⟩ | ⟨B, hB, S, hS, h⟩
  · rcases (h _ mem_subformulas_self).2 E rfl with h | ⟨E', hE', rfl⟩
    · refine ⟨∼(.atom (∼E)), .inl ⟨.atom (∼E), true, .atom (neg_mem_atoms_of_mem
        (Adequate.box h)), rfl⟩, ?_⟩
      have h₁ : L ⊢ □E 🡒 □(∼∼E) := Logic.box_mono (by cl_prover)
      have h₂ : L ⊢ □(∼∼E) 🡒 □E := Logic.box_mono (by cl_prover)
      change L ⊢ □E 🡘 □(∼∼E)
      cl_prover [h₁, h₂]
    · exact ⟨E', hE', by cl_prover⟩
  · simp at h
  obtain rfl := box_inj.mp h
  have hpre : ∀ A ∈ operands X, ∃ Z, LRClosure (atoms X) true Z ∧ Formula.ofModal Z = A :=
    fun _ h ↦ exists_of_mem_operands h
  choose f hf hf' using hpre
  let S₀ := S.filter (· ∈ operands X)
  let T₀ := (operands X).filter (◇· ∈ S)
  let S₁ := S₀.attach.image fun C ↦ f C.1 (Finset.mem_filter.mp C.2).2
  let T₁ := T₀.attach.image fun C ↦ f C.1 (Finset.mem_filter.mp C.2).1
  have hS₁ : ∀ C ∈ S₁, LRClosure (atoms X) true C := by
    intro C hC
    obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
    exact hf _ _
  have hT₁ : ∀ C ∈ T₁, LRClosure (atoms X) true C := by
    intro C hC
    obtain ⟨⟨D, hD⟩, -, rfl⟩ := Finset.mem_image.mp hC
    exact hf _ _
  refine ⟨f B hB 🡒 S₁.disj ⋎ (T₁.image (◇·)).disj, .inr ⟨f B hB, S₁, T₁, hf B hB, hS₁, hT₁, rfl⟩,
    ?_⟩
  have h₁ : L ⊢ S.disj 🡒 Formula.ofModal S₁.disj ⋎ Formula.ofModal (T₁.image (◇·)).disj := by
    apply left_Fdisj_intro
    intro C hC
    rcases Finset.mem_union.mp (hS hC) with hC' | hC'
    · have hC₀ : C ∈ S₀ := Finset.mem_filter.mpr ⟨hC, hC'⟩
      have : L ⊢ Formula.ofModal (f C hC') 🡒 Formula.ofModal S₁.disj :=
        imp_ofModal_disj (Finset.mem_image.mpr ⟨⟨C, hC₀⟩, Finset.mem_attach _ _, rfl⟩)
      rw [hf'] at this
      cl_prover [this]
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hC'
      have hG₀ : G ∈ T₀ := Finset.mem_filter.mpr ⟨hG, hC⟩
      have : L ⊢ Formula.ofModal (◇f G hG) 🡒 Formula.ofModal (T₁.image (◇·)).disj :=
        imp_ofModal_disj (Finset.mem_image_of_mem _ <|
          Finset.mem_image.mpr ⟨⟨G, hG₀⟩, Finset.mem_attach _ _, rfl⟩)
      change L ⊢ ◇Formula.ofModal (f G hG) 🡒 _ at this
      rw [hf'] at this
      cl_prover [this]
  have h₂ : L ⊢ Formula.ofModal S₁.disj 🡒 S.disj := by
    apply ofModal_disj_imp
    intro Z hZ
    obtain ⟨⟨C, hC⟩, -, rfl⟩ := Finset.mem_image.mp hZ
    rw [hf']
    exact right_Fdisj_intro _ (Finset.mem_filter.mp hC).1
  have h₃ : L ⊢ Formula.ofModal (T₁.image (◇·)).disj 🡒 S.disj := by
    apply ofModal_disj_imp
    intro Z hZ
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hZ
    obtain ⟨⟨G, hG⟩, -, rfl⟩ := Finset.mem_image.mp hW
    change L ⊢ ◇Formula.ofModal (f G _) 🡒 _
    rw [hf']
    exact right_Fdisj_intro _ (Finset.mem_filter.mp hG).2
  have h₄ : L ⊢ □(B 🡒 S.disj) 🡒 □(Formula.ofModal (f B hB 🡒 S₁.disj ⋎ (T₁.image (◇·)).disj)) := by
    apply Logic.box_mono
    change L ⊢ (B 🡒 S.disj) 🡒 (Formula.ofModal (f B hB) 🡒
      Formula.ofModal S₁.disj ⋎ Formula.ofModal (T₁.image (◇·)).disj)
    rw [hf']
    cl_prover [h₁]
  have h₅ : L ⊢ □(Formula.ofModal (f B hB 🡒 S₁.disj ⋎ (T₁.image (◇·)).disj)) 🡒 □(B 🡒 S.disj) := by
    apply Logic.box_mono
    change L ⊢ (Formula.ofModal (f B hB) 🡒
      Formula.ofModal S₁.disj ⋎ Formula.ofModal (T₁.image (◇·)).disj) 🡒 (B 🡒 S.disj)
    rw [hf']
    cl_prover [h₂, h₃]
  cl_prover [h₄, h₅]

omit [DecidableEq α] [Adequate X] in
lemma provable_ofModal_iff {Z Z' : ProvabilityLogic.Formula (Formula α)} (h : 𝐆𝐋 ⊢ Z 🡘 Z') :
    L ⊢ Formula.ofModal Z 🡘 Formula.ofModal Z' :=
  Logic.provable_ofModal h

omit [Adequate X] [L.ExtendsGL] in
private lemma exists_and_box_neg {W₀ : ProvabilityLogic.Formula (Formula α)}
    (hW₀ : LRClosure (atoms X) true W₀) {Y : Finset (Formula α)}
    (hY : ∀ E ∈ Y, ∃ b Z, LRClosure (atoms X) b Z ∧ L ⊢ E 🡘 □(∼Formula.ofModal Z)) :
    ∃ W, LRClosure (atoms X) true W ∧ L ⊢ Formula.ofModal W 🡘 Formula.ofModal W₀ ⋏ Y.conj := by
  induction Y using Finset.induction_on with
  | empty => exact ⟨W₀, hW₀, by simp only [Finset.conj_empty]; cl_prover⟩
  | @insert E Y _ ih =>
    obtain ⟨W, hW, h⟩ := ih fun E hE ↦ hY E (Finset.mem_insert_of_mem hE)
    obtain ⟨b, Z, hZ, hE⟩ := hY E (Finset.mem_insert_self _ _)
    refine ⟨W ⋏ □(∼Z), .and_box_neg hW hZ, ?_⟩
    have c₁ : L ⊢ (insert E Y).conj 🡒 E ⋏ Y.conj := CinsertFConjKFConj
    have c₂ : L ⊢ E ⋏ Y.conj 🡒 (insert E Y).conj := CKFConjinsertFConj
    change L ⊢ Formula.ofModal W ⋏ □(∼Formula.ofModal Z) 🡘 _
    cl_prover [h, hE, c₁, c₂]

omit [Adequate X] [L.ExtendsGL] in
private lemma exists_and_box_imp {b₀ : Bool} {W₀ : ProvabilityLogic.Formula (Formula α)}
    (hW₀ : LRClosure (atoms X) b₀ W₀) {Y : Finset (Formula α)}
    (hY : ∀ E ∈ Y, ∃ G, ∃ S T : Finset (ProvabilityLogic.Formula (Formula α)),
      LRClosure (atoms X) true G ∧ (∀ C ∈ S, LRClosure (atoms X) true C) ∧
        (∀ C ∈ T, LRClosure (atoms X) true C) ∧
        L ⊢ E 🡘 □(Formula.ofModal (G 🡒 S.disj ⋎ (T.image (◇·)).disj))) :
    ∃ b W, LRClosure (atoms X) b W ∧
      L ⊢ Formula.ofModal W 🡘 Formula.ofModal W₀ ⋏ Y.conj := by
  induction Y using Finset.induction_on with
  | empty => exact ⟨b₀, W₀, hW₀, by simp only [Finset.conj_empty]; cl_prover⟩
  | @insert E Y _ ih =>
    obtain ⟨b, W, hW, h⟩ := ih fun E hE ↦ hY E (Finset.mem_insert_of_mem hE)
    obtain ⟨G, S, T, hG, hS, hT, hE⟩ := hY E (Finset.mem_insert_self _ _)
    refine ⟨false, W ⋏ □(G 🡒 S.disj ⋎ (T.image (◇·)).disj), .and_box_imp hW hG hS hT, ?_⟩
    have c₁ : L ⊢ (insert E Y).conj 🡒 E ⋏ Y.conj := CinsertFConjKFConj
    have c₂ : L ⊢ E ⋏ Y.conj 🡒 (insert E Y).conj := CKFConjinsertFConj
    change L ⊢ Formula.ofModal W ⋏ □(Formula.ofModal (G 🡒 S.disj ⋎ (T.image (◇·)).disj)) 🡘 _
    cl_prover [h, hE, c₁, c₂]

lemma exists_box_neg_of_mem_boxes {E : Formula α} (h : E ∈ boxes X) :
    ∃ b Z, LRClosure (atoms X) b Z ∧ L ⊢ E 🡘 □(∼Formula.ofModal Z) := by
  classical
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨hE, D, rfl⟩ := Finset.mem_filter.mp h
    refine ⟨true, .atom (∼D), .atom (neg_mem_atoms_of_mem (Adequate.box hE)), ?_⟩
    have h₁ : L ⊢ □D 🡒 □(∼∼D) := Logic.box_mono (by cl_prover)
    have h₂ : L ⊢ □(∼∼D) 🡒 □D := Logic.box_mono (by cl_prover)
    change L ⊢ □D 🡘 □(∼∼D)
    cl_prover [h₁, h₂]
  · obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_union.mp hZ with hZ | hZ
    · exact ⟨true, Z, lrClosure_of_mem_reps hZ, by cl_prover⟩
    · exact ⟨false, Z, lrClosure_of_mem_reps hZ, by cl_prover⟩

/-- A conjunction of an operand with `□`-formulas of `boxes X` is equivalent to an operand.

- [Ign91, Definition 6.1]
-/
lemma exists_mem_operands_iff_and_conj (hB : B ∈ operands X) {Y : Finset (Formula α)}
    (hY : Y ⊆ boxes X) : ∃ B' ∈ operands X, L ⊢ B' 🡘 B ⋏ Y.conj := by
  classical
  obtain ⟨W₀, hW₀, rfl⟩ := exists_of_mem_operands hB
  obtain ⟨W, hW, h⟩ := exists_and_box_neg (L := L) hW₀ fun E hE ↦
    exists_box_neg_of_mem_boxes (hY hE)
  obtain ⟨W', hW', h'⟩ := exists_mem_reps hW
  have h'' : L ⊢ Formula.ofModal W 🡘 Formula.ofModal W' := provable_ofModal_iff h'
  exact ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hW'), by cl_prover [h, h'']⟩

/-- A conjunction of an operand with `□`-formulas of `clmAdequateClosure X` is equivalent to a
formula `B'` with `□∼B'` in `boxes X`.

- [Ign91, Definition 6.1]
-/
lemma exists_box_neg_mem_boxes_iff_and_conj (hB : B ∈ operands X) {Y : Finset (Formula α)}
    (hY : ∀ E ∈ Y, E ∈ clmAdequateClosure X ∧ ∃ D, E = □D) :
    ∃ B', □(∼B') ∈ boxes X ∧ L ⊢ B' 🡘 B ⋏ Y.conj := by
  classical
  let P₁ : Formula α → Prop := fun E ↦
    ∃ b Z, LRClosure (atoms X) b Z ∧ L ⊢ E 🡘 □(∼Formula.ofModal Z)
  obtain ⟨W₀, hW₀, rfl⟩ := exists_of_mem_operands hB
  obtain ⟨W₁, hW₁, h₁⟩ := exists_and_box_neg (L := L) (Y := Y.filter P₁) hW₀ fun E hE ↦
    (Finset.mem_filter.mp hE).2
  obtain ⟨b, W₂, hW₂, h₂⟩ := exists_and_box_imp (L := L) (Y := Y.filter (¬P₁ ·)) hW₁ <| by
    intro E hE
    obtain ⟨hE, hn⟩ := Finset.mem_filter.mp hE
    obtain ⟨hE, D, rfl⟩ := hY E hE
    obtain ⟨E', hE', h⟩ := exists_isBoxBody_of_box_mem (L := L) hE
    rcases hE' with ⟨Z, b, hZ, rfl⟩ | ⟨G, S, T, hG, hS, hT, rfl⟩
    · exact (hn ⟨b, Z, hZ, h⟩).elim
    · exact ⟨G, S, T, hG, hS, hT, h⟩
  obtain ⟨W', hW', h'⟩ := exists_mem_reps hW₂
  have h₃ : L ⊢ Formula.ofModal W₂ 🡘 Formula.ofModal W' := provable_ofModal_iff h'
  have c₁ : L ⊢ Y.conj 🡒 (Y.filter P₁).conj ⋏ (Y.filter (¬P₁ ·)).conj := by
    have d₁ : L ⊢ Y.conj 🡒 (Y.filter P₁).conj := CFConjFConj_of_subset (Finset.filter_subset _ _)
    have d₂ : L ⊢ Y.conj 🡒 (Y.filter (¬P₁ ·)).conj :=
      CFConjFConj_of_subset (Finset.filter_subset _ _)
    cl_prover [d₁, d₂]
  have c₂ : L ⊢ (Y.filter P₁).conj ⋏ (Y.filter (¬P₁ ·)).conj 🡒 Y.conj := by
    have d : L ⊢ (Y.filter P₁ ∪ Y.filter (¬P₁ ·)).conj 🡒 Y.conj := by
      rw [Finset.filter_union_filter_not_eq]
      cl_prover
    have d' : L ⊢ (Y.filter P₁).conj ⋏ (Y.filter (¬P₁ ·)).conj 🡒
        (Y.filter P₁ ∪ Y.filter (¬P₁ ·)).conj := CKFconjFconjUnion
    cl_prover [d, d']
  refine ⟨Formula.ofModal W', Finset.mem_union_right _ (Finset.mem_image_of_mem _ ?_),
    by cl_prover [h₁, h₂, h₃, c₁, c₂]⟩
  cases b
  · exact Finset.mem_union_right _ hW'
  · exact Finset.mem_union_left _ hW'

end clmAdequateClosure

end

/-! ## The countermodel -/

section

open Entailment MaximalConsistentSet clmAdequateClosure

variable [DecidableEq α] {X : Finset (Formula α)}

private lemma literals_provable_conj {L : Logic α} [Entailment.Cl L] {Φ : Finset (Formula α)}
    {Γ : MaximalConsistentSet L Φ} {Y : Finset (Formula α)} (h : ∀ A ∈ Y, A ∈ Γ) :
    Γ.literals *⊢[L] Y.conj :=
  Context.weakening (fun A hA ↦ mem_literals (h A hA)) (FConj_DT.mp C_id)

namespace Veltman

/-- `y` contains the `□`-formulas of `boxes X` in `x` together with their bodies, and the sequence
of `x` is a proper initial segment of that of `y`.

- [Ign91, Definition 6.8]
-/
def CLMRel (X : Finset (Formula α)) (x y : IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X)) : Prop :=
  (∀ {A}, □A ∈ boxes X → □A ∈ x.set → A ∈ y.set ∧ □A ∈ y.set) ∧ x.seq <+: y.seq ∧
    x.seq.length < y.seq.length

namespace CLMRel

variable {x y z : IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X)}

lemma trans (h₁ : CLMRel X x y) (h₂ : CLMRel X y z) : CLMRel X x z :=
  ⟨fun hA hx ↦ h₂.1 hA (h₁.1 hA hx).2, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

lemma of_successor (h : Successor x.set y.set) (h₂ : x.seq <+: y.seq)
    (h₃ : x.seq.length < y.seq.length) : CLMRel X x y :=
  ⟨fun _ hx ↦ ⟨h.mem_of_box_mem hx, h.box_mem_of_box_mem hx⟩, h₂, h₃⟩

end CLMRel

/-- The model on indexed sets of `𝐂𝐋𝐌` over `clmAdequateClosure X` in which `y ≺[w] z` holds if `y`
and `z` are above `w` and have the same sequence, `z` contains the `□`-formulas of `boxes X` in
`y`, and `z` is a weak `C`-critical successor of `w` whenever `y` is one and its sequence is that
of `w` followed by `C`.

- [Ign91, Definition 6.8]
-/
def countermodelCLM (X : Finset (Formula α))
    [Nonempty (IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X))] :
    Model (IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X)) α where
  Rel' := CLMRel X
  S' w x y := CLMRel X w x ∧ CLMRel X w y ∧ x.seq = y.seq ∧
    (∀ {A}, □A ∈ boxes X → □A ∈ x.set → □A ∈ y.set) ∧
    ∀ C, x.seq = w.seq ++ [C] → WeakCriticalSuccessor C w.set x.set →
      WeakCriticalSuccessor C w.set y.set
  Val' x a := Formula.atom a ∈ x.set

namespace countermodelCLM

open Model Model.World

variable [Nonempty (IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X))]

instance : IsTrans _ (countermodelCLM X).Rel := ⟨fun _ _ _ ↦ CLMRel.trans⟩

instance : Std.Irrefl (countermodelCLM X).Rel := ⟨fun _ h ↦ (lt_irrefl _) h.2.2⟩

instance [Adequate X] : (countermodelCLM X).IsCL where
  rel_of_s_left h := h.1
  rel_of_s_right h := h.2.1
  s_refl h := ⟨h, h, rfl, fun _ hx ↦ hx, fun _ _ hx ↦ hx⟩
  s_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun hA hx ↦ h₂.2.2.2.1 hA (h₁.2.2.2.1 hA hx),
    fun C hC hx ↦ h₂.2.2.2.2 C (h₁.2.2.1 ▸ hC) (h₁.2.2.2.2 C hC hx)⟩

/-- - [Ign91, Proposition 6.9] -/
instance : (countermodelCLM X).HasM where
  rel_of_s_rel h₁ h₂ :=
    ⟨fun hA hx ↦ h₂.1 hA (h₁.2.2.2.1 hA hx), h₁.2.2.1 ▸ h₂.2.1, h₁.2.2.1 ▸ h₂.2.2⟩

variable [Adequate X] {x u : IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X)} {B C E : Formula α}

omit [Nonempty (IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X))] in
private lemma mem_operands_of_isRhdOperand (h : IsRhdOperand X B) : B ∈ operands X := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h.mem, h⟩)

omit [Nonempty (IndexedSet 𝐂𝐋𝐌 (clmAdequateClosure X))] [Adequate X] in
private lemma box_mem_boxes (h : □B ∈ X) : □B ∈ boxes X := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, B, rfl⟩)

/-- A `≺[x]`-successor of `u` containing `C` when `u` is a weak `E`-critical successor of `x`
whose sequence is that of `x` followed by `E`.

- [Ign91, Lemma 6.11]
-/
private lemma exists_s_of_weakCriticalSuccessor (hBC : B ▷ C ∈ X) (hx : B ▷ C ∈ x.set)
    (hxu : CLMRel X x u) (hB : B ∈ u.set) (hseq : u.seq = x.seq ++ [E])
    (hcrit : WeakCriticalSuccessor E x.set u.set) :
    ∃ z, (countermodelCLM X).S x u z ∧ C ∈ z.set := by
  classical
  let Y₀ := u.set.prebox.filter (□· ∈ boxes X)
  have hY : Y₀.image (□·) ⊆ boxes X := by
    intro A hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_filter.mp hD).2
  obtain ⟨B', hB', hBB'⟩ := exists_mem_operands_iff_and_conj (L := 𝐂𝐋𝐌)
    (mem_operands_of_isRhdOperand (.of_rhd_left hBC)) hY
  obtain ⟨C', hC', hCC'⟩ := exists_mem_operands_iff_and_conj (L := 𝐂𝐋𝐌)
    (mem_operands_of_isRhdOperand (.of_rhd_right hBC)) hY
  have hbox : 𝐂𝐋𝐌 ⊢ □Y₀.conj 🡘 (Y₀.image (□·)).conj := Logic.box_iff_conj_image_box
  have h₁ : 𝐂𝐋𝐌 ⊢ B ▷ C 🡒 (B ⋏ □Y₀.conj) ▷ (C ⋏ □Y₀.conj) := Logic.CLM.axiomM
  have h₂ : 𝐂𝐋𝐌 ⊢ (B ⋏ □Y₀.conj) ▷ (C ⋏ □Y₀.conj) 🡒 B' ▷ (C ⋏ □Y₀.conj) :=
    Logic.ofCLAxioms.rhd_anti_left (by cl_prover [hBB', hbox])
  have h₃ : 𝐂𝐋𝐌 ⊢ B' ▷ (C ⋏ □Y₀.conj) 🡒 B' ▷ C' :=
    Logic.ofCLAxioms.rhd_mono_right (by cl_prover [hCC', hbox])
  have hx' : B' ▷ C' ∈ x.set :=
    (mem_iff_provable (rhd_mem_of_mem_operands hB' hC')).mpr <|
      Context.of (C_trans h₁ (C_trans h₂ h₃)) ⨀ Context.by_axm (mem_literals hx)
  have hYu : ∀ A ∈ Y₀.image (□·), A ∈ u.set := by
    intro A hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hA
    exact mem_prebox.mp (Finset.mem_filter.mp hD).1
  have hB'u : B' ∈ u.set :=
    (mem_iff_provable (mem_operands_iff.mpr hB').mem).mpr <| Context.of (K_right hBB') ⨀
      K_intro (Context.by_axm (mem_literals hB)) (literals_provable_conj hYu)
  have hE : IsRhdOperand (clmAdequateClosure X) E := u.isRhdOperand_of_mem_seq E (by simp [hseq])
  obtain ⟨Θ, hΘ, hC'Θ, -⟩ := hcrit.exists_weakCriticalSuccessor_mem_not_mem hE hx' hB'u
  have hlen : u.seq.length ≤ Θ.prebox.card := by
    rw [hseq, List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt <|
      x.length_seq_le.trans_lt (Finset.card_lt_card hΘ.toSuccessor.prebox_ssubset)
  have hC'C : 𝐂𝐋𝐌 ⊢ C' 🡒 C ⋏ (Y₀.image (□·)).conj := K_left hCC'
  refine ⟨⟨Θ, u.seq, u.isRhdOperand_of_mem_seq, hlen⟩, ⟨hxu,
    .of_successor hΘ.toSuccessor hxu.2.1 hxu.2.2, rfl, fun {A} hA hu ↦ ?_, fun E' hE' _ ↦ ?_⟩, ?_⟩
  · have h : □A ∈ Y₀.image (□·) :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨mem_prebox.mpr hu, hA⟩)
    exact (mem_iff_provable (mem_of_mem_boxes hA)).mpr <|
      Context.of (C_trans hC'C (C_trans and₂ (left_Fconj_intro h))) ⨀
        Context.by_axm (mem_literals hC'Θ)
  · obtain rfl : E = E' := by simpa [hseq] using hE'
    exact hΘ
  · exact (mem_iff_provable (subset (Adequate.rhd_right hBC))).mpr <|
      Context.of (C_trans hC'C and₁) ⨀ Context.by_axm (mem_literals hC'Θ)

/-- A `≺[x]`-successor of `u` containing `C` when `u` is not a weak `E`-critical successor of `x`
whose sequence is that of `x` followed by `E`.

- [Ign91, Lemma 6.11]
-/
private lemma exists_s_of_not_weakCriticalSuccessor (hBC : B ▷ C ∈ X) (hx : B ▷ C ∈ x.set)
    (hxu : CLMRel X x u) (hB : B ∈ u.set)
    (hn : ¬∃ E, u.seq = x.seq ++ [E] ∧ WeakCriticalSuccessor E x.set u.set) :
    ∃ z, (countermodelCLM X).S x u z ∧ C ∈ z.set := by
  classical
  let Y₀ := u.set.prebox
  have hYu : ∀ A ∈ Y₀.image (□·), A ∈ u.set := by
    intro A hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hA
    exact mem_prebox.mp hD
  obtain ⟨B'', hK, hB''⟩ := exists_box_neg_mem_boxes_iff_and_conj (L := 𝐂𝐋𝐌)
    (mem_operands_of_isRhdOperand (.of_rhd_left hBC)) (Y := Y₀.image (□·)) fun E hE ↦ by
      refine ⟨mem_of_mem (hYu E hE), ?_⟩
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hE
      exact ⟨D, rfl⟩
  have hK' := mem_of_mem_boxes hK
  have hnx : □(∼B'') ∉ x.set := by
    intro h
    apply not_mem_of_neg_mem (hxu.1 hK h).1
    exact (mem_iff_provable (Adequate.imp_left (Adequate.box hK'))).mpr <|
      Context.of (K_right hB'') ⨀
        K_intro (Context.by_axm (mem_literals hB)) (literals_provable_conj hYu)
  have hbox : 𝐂𝐋𝐌 ⊢ □Y₀.conj 🡘 (Y₀.image (□·)).conj := Logic.box_iff_conj_image_box
  have h₁ : x.set.literals *⊢[𝐂𝐋𝐌] ∼□(∼B'') := provable_neg_of_not_mem hK' hnx
  have h₂ : 𝐂𝐋𝐌 ⊢ □(∼(B ⋏ □Y₀.conj)) 🡒 □(∼B'') := Logic.box_mono (by cl_prover [hB'', hbox])
  have h₃ : 𝐂𝐋𝐌 ⊢ B ▷ C 🡒 (B ⋏ □Y₀.conj) ▷ (C ⋏ □Y₀.conj) := Logic.CLM.axiomM
  have h₄ : 𝐂𝐋𝐌 ⊢ (B ⋏ □Y₀.conj) ▷ (C ⋏ □Y₀.conj) 🡒 ◇(B ⋏ □Y₀.conj) 🡒 ◇(C ⋏ □Y₀.conj) :=
    Logic.ofCLAxioms.axiomJ4
  have hdia : x.set.literals *⊢[𝐂𝐋𝐌] ∼□(∼(C ⋏ □Y₀.conj)) := by
    have h₅ := Context.of (Γ := x.set.literals) h₂
    have h₆ := Context.of (Γ := x.set.literals) h₃
    have h₇ := Context.of (Γ := x.set.literals) h₄
    have h₈ : x.set.literals *⊢[𝐂𝐋𝐌] B ▷ C := Context.by_axm (mem_literals hx)
    change x.set.literals *⊢[𝐂𝐋𝐌] (B ⋏ □Y₀.conj) ▷ (C ⋏ □Y₀.conj) 🡒
      ∼□(∼(B ⋏ □Y₀.conj)) 🡒 ∼□(∼(C ⋏ □Y₀.conj)) at h₇
    cl_prover [h₁, h₅, h₆, h₇, h₈]
  let T : FormulaSet α := {A | □A ∈ x.set}
  let Z₀ : FormulaSet α := insert (C ⋏ □Y₀.conj) (T ∪ (□·) '' T)
  have hZ₀ : Z₀ *⊬[𝐂𝐋𝐌] ⊥ := by
    intro h
    have h₁ : (T ∪ (□·) '' T) *⊢[𝐂𝐋𝐌] ∼(C ⋏ □Y₀.conj) := Context.deduct h
    have h₂ : x.set.literals *⊢[𝐂𝐋𝐌] □(∼(C ⋏ □Y₀.conj)) :=
      Context.weakening (by rintro _ ⟨A, hA, rfl⟩; exact mem_literals hA)
        (Logic.box_of_provable h₁)
    exact consistent_literals <| by
      change x.set.literals *⊢[𝐂𝐋𝐌] ⊥
      cl_prover [h₂, hdia]
  obtain ⟨Θ, hΘ⟩ := exists_consistent_union (Φ := clmAdequateClosure X) hZ₀
  have hm {A} (hA : A ∈ clmAdequateClosure X) (h : Z₀ *⊢[𝐂𝐋𝐌] A) : A ∈ Θ :=
    mem_of_provable hΘ hA h
  have hCY : Z₀ *⊢[𝐂𝐋𝐌] C ⋏ □Y₀.conj := Context.by_axm (Set.mem_insert _ _)
  have hboxΘ {A} (hA : A ∈ Y₀) : □A ∈ Θ :=
    hm (mem_of_mem (mem_prebox.mp hA)) <|
      Context.of (C_trans and₂ (Logic.box_mono (left_Fconj_intro hA))) ⨀ hCY
  have hlen : u.seq.length ≤ Θ.prebox.card :=
    u.length_seq_le.trans (Finset.card_le_card fun A hA ↦ mem_prebox.mpr (hboxΘ hA))
  have hxz : CLMRel X x ⟨Θ, u.seq, u.isRhdOperand_of_mem_seq, hlen⟩ := by
    refine ⟨fun {A} _ hA ↦ ⟨hm (Adequate.box (mem_of_mem hA)) (Context.by_axm ?_),
      hm (mem_of_mem hA) (Context.by_axm ?_)⟩, hxu.2.1, hxu.2.2⟩
    · exact Set.mem_insert_of_mem _ (.inl hA)
    · exact Set.mem_insert_of_mem _ (.inr ⟨A, hA, rfl⟩)
  exact ⟨⟨Θ, u.seq, u.isRhdOperand_of_mem_seq, hlen⟩,
    ⟨hxu, hxz, rfl, fun {A} _ hu ↦ hboxΘ (mem_prebox.mpr hu), fun E hE hcrit ↦
      (hn ⟨E, hE, hcrit⟩).elim⟩,
    hm (subset (Adequate.rhd_right hBC)) (Context.of and₁ ⨀ hCY)⟩

/-- - [Ign91, Lemma 6.11] -/
lemma truthlemma {x : (countermodelCLM X).World} {A : Formula α} (hA : A ∈ X) :
    x ⊩ A ↔ A ∈ x.set := by
  induction A generalizing x with
  | atom a => rfl
  | falsum => exact ⟨False.elim, fun h ↦ bot_not_mem h⟩
  | imp A B ihA ihB =>
    have hA' := Adequate.imp_left hA
    have hB' := Adequate.imp_right hA
    rw [imp_mem_iff (subset hA) (subset hA') (subset hB'), ← ihA hA', ← ihB hB']
    rfl
  | box A ih =>
    have hA' := Adequate.box hA
    constructor
    · intro h
      by_contra hn
      obtain ⟨Δ, hΔ, hAΔ⟩ := exists_successor_of_box_not_mem (subset hA) hn
      have hlen : (x.seq ++ [⊥]).length ≤ Δ.prebox.card := by
        simpa using Nat.succ_le_of_lt
          (x.length_seq_le.trans_lt (Finset.card_lt_card hΔ.prebox_ssubset))
      have hseq : ∀ C ∈ x.seq ++ [⊥], IsRhdOperand (clmAdequateClosure X) C := by
        intro C hC
        rcases List.mem_append.mp hC with hC | hC
        · exact x.isRhdOperand_of_mem_seq C hC
        · obtain rfl := List.mem_singleton.mp hC
          exact .bot
      exact not_mem_of_provable_neg hAΔ (Context.by_axm rfl) <| (ih hA').mp <|
        h ⟨Δ, x.seq ++ [⊥], hseq, hlen⟩ (.of_successor hΔ (List.prefix_append _ _) (by simp))
    · intro h y hxy
      exact (ih hA').mpr (hxy.1 (box_mem_boxes hA) h).1
  | rhd B C ihB ihC =>
    have hB := Adequate.rhd_left hA
    have hC := Adequate.rhd_right hA
    constructor
    · intro h
      by_contra hn
      obtain ⟨Δ, hΔ, hBΔ⟩ := exists_weakCriticalSuccessor_of_rhd_not_mem (subset hA) hn
      have hC' : IsRhdOperand (clmAdequateClosure X) C := .of_rhd_right (subset hA)
      have hlen : (x.seq ++ [C]).length ≤ Δ.prebox.card := by
        simpa using Nat.succ_le_of_lt
          (x.length_seq_le.trans_lt (Finset.card_lt_card hΔ.prebox_ssubset))
      have hseq : ∀ D ∈ x.seq ++ [C], IsRhdOperand (clmAdequateClosure X) D := by
        intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact x.isRhdOperand_of_mem_seq D hD
        · obtain rfl := List.mem_singleton.mp hD
          exact hC'
      obtain ⟨z, hS, hz⟩ := h ⟨Δ, x.seq ++ [C], hseq, hlen⟩
        (.of_successor hΔ.toSuccessor (List.prefix_append _ _) (by simp)) ((ihB hB).mpr hBΔ)
      exact (hS.2.2.2.2 C rfl hΔ).not_mem
        ((mem_iff_provable (Adequate.rhd_mem hC' hC')).mpr
          (Context.of Logic.ofCLAxioms.rhd_refl)) ((ihC hC).mp hz)
    · intro h u hxu hu
      by_cases hc : ∃ E, u.seq = x.seq ++ [E] ∧ WeakCriticalSuccessor E x.set u.set
      · obtain ⟨E, hseq, hcrit⟩ := hc
        obtain ⟨z, hS, hz⟩ :=
          exists_s_of_weakCriticalSuccessor hA h hxu ((ihB hB).mp hu) hseq hcrit
        exact ⟨z, hS, (ihC hC).mpr hz⟩
      · obtain ⟨z, hS, hz⟩ := exists_s_of_not_weakCriticalSuccessor hA h hxu ((ihB hB).mp hu) hc
        exact ⟨z, hS, (ihC hC).mpr hz⟩

end countermodelCLM

end Veltman

end

/-! ## Completeness -/

namespace Logic

open Entailment Veltman Veltman.Model Veltman.Model.World

variable {α : Type} {A : Formula α}

/-- - [Ign91, Lemma 3.5]
- [Ign91, Theorem 4]
-/
theorem CLM.semantics_TFAE : [
    𝐂𝐋𝐌 ⊢ A,
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [M.IsCL] → [M.HasM] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsCL] → [M.HasM] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 2 := fun h _ _ _ _ _ ↦ CLM.sound h
  tfae_have 2 → 3 := fun h _ _ _ M _ _ ↦ h M
  tfae_have 3 → 1 := by
    intro h
    classical
    by_contra hA
    have : Entailment.Consistent (𝐂𝐋𝐌 : Logic α) := .of_unprovable hA
    let X := adequateClosure {A}
    have hX : ({∼A} : FormulaSet α) *⊬[𝐂𝐋𝐌] ⊥ := by
      intro h₁
      apply hA
      have h₂ : 𝐂𝐋𝐌 ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁
      cl_prover [h₂]
    obtain ⟨Γ, hΓ⟩ := MaximalConsistentSet.exists_consistent_union
      (Φ := clmAdequateClosure X) hX
    have hAX : A ∈ X := adequateClosure.subset (by simp)
    exact MaximalConsistentSet.not_mem_of_provable_neg hΓ (Context.by_axm rfl) <|
      (countermodelCLM.truthlemma hAX).mp <| h (countermodelCLM X) ⟨Γ, [], by simp, by simp⟩
  tfae_finish

theorem CLM.iff_valid :
    𝐂𝐋𝐌 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [M.IsCL] → [M.HasM] → M ⊧ A :=
  CLM.semantics_TFAE.out 1 2

/-- - [Ign91, Lemma 3.5]
- [Ign91, Theorem 4]
-/
theorem CLM.iff_valid_finite :
    𝐂𝐋𝐌 ⊢ A ↔ ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α),
      [M.IsCL] → [M.HasM] → M ⊧ A :=
  CLM.semantics_TFAE.out 1 3

/-! ## Strict inclusions -/

instance : (Veltman.countermodelJ5 α).HasM := ⟨by omega⟩

open Veltman

instance : (𝐂𝐋 : Logic ℕ) ⪱ 𝐂𝐋𝐌 :=
  .of_unprovable_provable (φ := Axioms.M (#0) (#1) (#2))
    (fun h ↦ countermodelM.not_models_axiomM (CL.sound h)) CLM.axiomM

instance : (𝐂𝐋𝐌 : Logic ℕ) ⪱ 𝐈𝐋𝐌 :=
  .of_unprovable_provable (φ := Axioms.J5 (□⊥))
    (fun h ↦ countermodelJ5.not_models_axiomJ5 (CLM.sound (M := countermodelJ5 ℕ) h))
    ofILAxioms.axiomJ5

end Logic

end FFL.InterpretabilityLogic
