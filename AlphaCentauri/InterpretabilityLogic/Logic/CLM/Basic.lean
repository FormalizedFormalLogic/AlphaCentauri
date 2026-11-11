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

end clmAdequateClosure

end

end FFL.InterpretabilityLogic
