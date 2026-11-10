module

public import AlphaCentauri.InterpretabilityLogic.Formula
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import AlphaCentauri.InterpretabilityLogic.Logic.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# A sequent calculus for $\mathbf{IL}$

Subformulas, sequents of finite sets of formulas, and the extension of a sequent on which a
predicate fails to a saturated one. A cut-free sequent calculus for $\mathbf{IL}$ in the language
with a primitive `□`, whose modal rules are those of $\mathbf{GIL}$, with `A ▷ ⊥` written `□∼A`, the
boxes on the left treated as in the calculus of $\mathbf{GL}$, and a rule for `□` on the right. A
sequent derivable in it has the implication from the conjunction of its antecedent to the
disjunction of its succedent derivable in $\mathbf{IL}$.

## References

- [HSS25a]
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

abbrev FormulaFinset (α : Type*) := Finset (Formula α)

namespace FormulaFinset

variable {α : Type*} {Γ : FormulaFinset α} {A B : Formula α}

/-- The formulas `A` with `□A ∈ Γ`. -/
noncomputable def prebox (Γ : FormulaFinset α) : FormulaFinset α :=
  Γ.preimage (□·) fun _ _ _ _ h ↦ Formula.box_inj.mp h

@[simp, grind =] lemma mem_prebox : A ∈ Γ.prebox ↔ □A ∈ Γ := Finset.mem_preimage

variable [DecidableEq α]

abbrev box (Γ : FormulaFinset α) : FormulaFinset α := Γ.image (□·)

/-- The formulas `□∼A` for `A ∈ Γ`. -/
abbrev boxNeg (Γ : FormulaFinset α) : FormulaFinset α := Γ.image fun A ↦ □(∼A)

@[grind .] lemma box_prebox_subset : Γ.prebox.box ⊆ Γ := by
  intro A hA;
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA;
  exact mem_prebox.mp hB;

def subformulas (Γ : FormulaFinset α) : FormulaFinset α := Γ.biUnion Formula.subformulas

@[grind .] lemma subset_subformulas : Γ ⊆ Γ.subformulas :=
  fun A hA ↦ Finset.mem_biUnion.mpr ⟨A, hA, Formula.mem_subformulas_self⟩

@[grind →]
lemma mem_subformulas_subformulas {C : Formula α} (hB : B ∈ Γ.subformulas)
    (hC : C ∈ B.subformulas) : C ∈ Γ.subformulas := by
  obtain ⟨A, hA, hBA⟩ := Finset.mem_biUnion.mp hB;
  exact Finset.mem_biUnion.mpr ⟨A, hA, Formula.subformulas_subset_of_mem hBA hC⟩

end FormulaFinset

structure Sequent (α : Type*) where
  ant : FormulaFinset α
  suc : FormulaFinset α

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

variable {α : Type*} {S T : Sequent α}

structure Subset (S T : Sequent α) : Prop where
  ant : S.ant ⊆ T.ant
  suc : S.suc ⊆ T.suc

instance : HasSubset (Sequent α) := ⟨Subset⟩

@[simp] lemma subset_iff : S ⊆ T ↔ S.ant ⊆ T.ant ∧ S.suc ⊆ T.suc :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

structure Saturated (S : Sequent α) : Prop where
  impL : ∀ {A B}, A 🡒 B ∈ S.ant → A ∈ S.suc ∨ B ∈ S.ant
  impR : ∀ {A B}, A 🡒 B ∈ S.suc → A ∈ S.ant ∧ B ∈ S.suc

variable [DecidableEq α]

def subformulas (S : Sequent α) : FormulaFinset α := (S.ant ∪ S.suc).subformulas

end Sequent

namespace IL

variable {α : Type*} [DecidableEq α]

/-- The first components of a list of pairs of formulas. -/
def antecedents (l : List (Formula α × Formula α)) : FormulaFinset α := (l.map Prod.fst).toFinset

/-- The formulas `A ▷ B` for the pairs `(A, B)` of a list. -/
def rhdFormulas (l : List (Formula α × Formula α)) : FormulaFinset α :=
  (l.map fun p ↦ p.1 ▷ p.2).toFinset

/-- The sequent `D, □∼D, Γ, □Γ, □∼N ⟹ N`. -/
def witness (Γ N : FormulaFinset α) (D : Formula α) : Sequent α :=
  insert D (insert (□(∼D)) (Γ ∪ Γ.box ∪ N.boxNeg)) ⟹ N

@[simp, grind =] lemma antecedents_nil : antecedents ([] : List (Formula α × Formula α)) = ∅ := rfl

@[simp, grind =] lemma antecedents_cons {p : Formula α × Formula α} {l} :
    antecedents (p :: l) = insert p.1 (antecedents l) := by simp [antecedents]

@[simp, grind =] lemma mem_antecedents {l : List (Formula α × Formula α)} {A : Formula α} :
    A ∈ antecedents l ↔ ∃ B, (A, B) ∈ l := by simp [antecedents]

@[simp, grind =] lemma rhdFormulas_nil : rhdFormulas ([] : List (Formula α × Formula α)) = ∅ := rfl

@[simp, grind =] lemma rhdFormulas_cons {p : Formula α × Formula α} {l} :
    rhdFormulas (p :: l) = insert (p.1 ▷ p.2) (rhdFormulas l) := by simp [rhdFormulas]

@[simp, grind =] lemma mem_rhdFormulas {l : List (Formula α × Formula α)} {C : Formula α} :
    C ∈ rhdFormulas l ↔ ∃ A B, (A, B) ∈ l ∧ C = A ▷ B := by
  simp [rhdFormulas, eq_comm]

/-- The cut-free sequent calculus for $\mathbf{IL}$: the rules `rhd` and `box` take, for a list
`l` of pairs `(C, D)` of the formulas `C ▷ D` on the left, one premise for each pair and one for the
formula on the right, the premise of a pair mentioning the antecedents of the pairs after it.

- [HSS25a, Definition 3.1]
-/
inductive Gentzen : Sequent α → Prop
  | axm (A) : Gentzen ({A} ⟹ {A})
  | botL : Gentzen ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Gentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → Gentzen (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Gentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → Gentzen (Γ ⟹ Δ')
  | impL {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A 🡒 B) Δ)
  | rhd {Γ : FormulaFinset α} {l : List (Formula α × Formula α)} {A B : Formula α} :
    (∀ l₁ p l₂, l = l₁ ++ p :: l₂ → Gentzen (witness Γ (insert B (antecedents l₂)) p.2)) →
    Gentzen (witness Γ (insert B (antecedents l)) A) →
    Gentzen (Γ.box ∪ rhdFormulas l ⟹ {A ▷ B})
  | box {Γ : FormulaFinset α} {l : List (Formula α × Formula α)} {B : Formula α} :
    (∀ l₁ p l₂, l = l₁ ++ p :: l₂ → Gentzen (witness Γ (antecedents l₂) p.2)) →
    Gentzen (insert (□B) (Γ ∪ Γ.box ∪ (antecedents l).boxNeg) ⟹ insert B (antecedents l)) →
    Gentzen (Γ.box ∪ rhdFormulas l ⟹ {□B})

@[inherit_doc] notation:45 "⊢ᴳ[𝐈𝐋] " S:50 => Gentzen S

notation:45 "⊬ᴳ[𝐈𝐋] " S:50 => ¬Gentzen S

namespace Gentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {S : Sequent α}

lemma union (A) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᴳ[𝐈𝐋] Γ ⟹ Δ :=
  wkR (wkL (axm A) (by simpa)) (by simpa)

lemma union' (A) (hΓ : A ∈ S.ant) (hΔ : A ∈ S.suc) : ⊢ᴳ[𝐈𝐋] S := union A hΓ hΔ

lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[𝐈𝐋] Γ ⟹ Δ := wkR (wkL botL (by simpa)) (by simp)

lemma wk (h : ⊢ᴳ[𝐈𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐈𝐋] Γ' ⟹ Δ' := wkR (wkL h hΓ) hΔ

/-- Every sequent within `P` not derivable extends to a saturated one within `P` on which `D`
fails, provided `P` contains the components of its implications. -/
lemma exists_saturated {P : FormulaFinset α}
    (hP : ∀ {A B}, A 🡒 B ∈ P → A ∈ P ∧ B ∈ P) {S₀ : Sequent α} (h₀ : ⊬ᴳ[𝐈𝐋] S₀)
    (hant : S₀.ant ⊆ P) (hsuc : S₀.suc ⊆ P) :
    ∃ S, S₀ ⊆ S ∧ ⊬ᴳ[𝐈𝐋] S ∧ S.Saturated ∧ S.ant ⊆ P ∧ S.suc ⊆ P := by
  classical
  let C := (P.powerset ×ˢ P.powerset).filter
    fun p ↦ S₀.ant ⊆ p.1 ∧ S₀.suc ⊆ p.2 ∧ ¬Gentzen (p.1 ⟹ p.2);
  have hC : (S₀.ant, S₀.suc) ∈ C := by simp [C, hant, hsuc, h₀];
  obtain ⟨⟨Γ, Δ⟩, hp, hmax⟩ := C.exists_max_image (fun p ↦ p.1.card + p.2.card) ⟨_, hC⟩;
  simp only [C, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp;
  obtain ⟨⟨hΓ, hΔ⟩, h₁, h₂, hD'⟩ := hp;
  have grow : ∀ {Γ' Δ'}, Γ ⊆ Γ' → Δ ⊆ Δ' → Γ' ⊆ P → Δ' ⊆ P → ¬Gentzen (Γ' ⟹ Δ') →
      Γ' = Γ ∧ Δ' = Δ := by
    intro Γ' Δ' hΓ' hΔ' hΓP hΔP hn;
    have hle := hmax (Γ', Δ') (by simp [C, hΓP, hΔP, h₁.trans hΓ', h₂.trans hΔ', hn]);
    have := Finset.card_le_card hΓ';
    have := Finset.card_le_card hΔ';
    exact ⟨Finset.eq_of_subset_of_card_le hΓ' (by simp at hle; omega) |>.symm,
      Finset.eq_of_subset_of_card_le hΔ' (by simp at hle; omega) |>.symm⟩;
  use Γ ⟹ Δ;
  and_intros;
  · exact ⟨h₁, h₂⟩;
  · exact hD';
  · constructor;
    · intro A B hAB;
      have hA := (hP (hΓ hAB)).1;
      have hB := (hP (hΓ hAB)).2;
      by_cases hl : Gentzen (Γ ⟹ insert A Δ);
      · by_cases hr : Gentzen (insert B Γ ⟹ Δ);
        · exact absurd (by simpa [Finset.insert_eq_of_mem hAB] using impL hl hr) hD';
        · right;
          rw [← (grow (Finset.subset_insert B Γ) subset_rfl
            (Finset.insert_subset hB hΓ) hΔ hr).1];
          exact Finset.mem_insert_self B Γ;
      · left;
        rw [← (grow subset_rfl (Finset.subset_insert A Δ) hΓ
          (Finset.insert_subset hA hΔ) hl).2];
        exact Finset.mem_insert_self A Δ;
    · intro A B hAB;
      have hA := (hP (hΔ hAB)).1;
      have hB := (hP (hΔ hAB)).2;
      have hn : ¬Gentzen (insert A Γ ⟹ insert B Δ) := fun h ↦
        hD' (by simpa [Finset.insert_eq_of_mem hAB] using impR h);
      obtain ⟨e₁, e₂⟩ := grow (Finset.subset_insert A Γ) (Finset.subset_insert B Δ)
        (Finset.insert_subset hA hΓ) (Finset.insert_subset hB hΔ) hn;
      rw [← e₁, ← e₂];
      exact ⟨Finset.mem_insert_self A Γ, Finset.mem_insert_self B Δ⟩;
  · exact hΓ;
  · exact hΔ;

end Gentzen

end IL

open Entailment Formula IL

variable {α : Type*}

namespace IL.Gentzen

open Logic Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {A B C D X Y : Formula α}

private lemma rhd_trans_left (h : ofAxioms 𝔸 ⊢ A ▷ B) : ofAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have : ofAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h, this];

private lemma rhd_of_cases {X₁ X₂ X₃ : Formula α} (h : ofAxioms 𝔸 ⊢ X 🡒 (X₁ ⋎ X₂) ⋎ X₃) :
    ofAxioms 𝔸 ⊢ X₁ ▷ Y 🡒 X₂ ▷ Y 🡒 X₃ ▷ Y 🡒 X ▷ Y := by
  have h₁ : ofAxioms 𝔸 ⊢ X₁ ▷ Y ⋏ X₂ ▷ Y 🡒 (X₁ ⋎ X₂) ▷ Y := axiomJ3;
  have h₂ : ofAxioms 𝔸 ⊢ (X₁ ⋎ X₂) ▷ Y ⋏ X₃ ▷ Y 🡒 ((X₁ ⋎ X₂) ⋎ X₃) ▷ Y := axiomJ3;
  cl_prover [rhd_anti_left (C := Y) h, h₁, h₂];

variable [DecidableEq α] {Γ N : FormulaFinset α}

private lemma box_conj : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : ofAxioms 𝔸 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact C_of_conseq (nec this);
  | insert A Γ _ ih =>
    have h₁ : ofAxioms 𝔸 ⊢
        (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ofAxioms 𝔸 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

private lemma box_conj_box : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.box.conj := by
  have h₁ : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 Γ.box.box.conj := by
    apply right_Fconj_intro;
    intro B hB;
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
    exact C_trans (left_Fconj_intro hC) axiom4;
  have h₂ : ofAxioms 𝔸 ⊢ Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
  cl_prover [h₁, h₂];

private lemma rhd_of_box_imp (N : FormulaFinset α) (X Y : Formula α) :
    ofAxioms 𝔸 ⊢
      (N.image (· ▷ Y)).conj 🡒 □(X ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) 🡒 X ▷ Y := by
  induction N using Finset.induction_on generalizing X with
  | empty =>
    have h : ofAxioms 𝔸 ⊢ □(X ⋏ (FormulaFinset.boxNeg ∅).conj 🡒 (∅ : FormulaFinset α).disj)
        🡒 □(X 🡒 Y) := box_mono (by
          simp only [Finset.image_empty, Finset.conj_empty, Finset.disj_empty];
          cl_prover);
    have h' : ofAxioms 𝔸 ⊢ □(X 🡒 Y) 🡒 X ▷ Y := axiomJ1;
    cl_prover [h, h'];
  | insert a N _ ih =>
    have h₁ : ofAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 a ▷ Y ⋏ (N.image (· ▷ Y)).conj := by
      rw [Finset.image_insert];
      exact CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢
        □(∼a) ⋏ (FormulaFinset.boxNeg N).conj 🡒 (FormulaFinset.boxNeg (insert a N)).conj := by
      rw [FormulaFinset.boxNeg, FormulaFinset.boxNeg, Finset.image_insert];
      exact CKFConjinsertFConj;
    have h₃ : ofAxioms 𝔸 ⊢ (insert a N).disj 🡒 a ⋎ N.disj := CinsertFDisjAFDisj;
    have h₄ : ofAxioms 𝔸 ⊢ □(X ⋏ (FormulaFinset.boxNeg (insert a N)).conj 🡒 (insert a N).disj) 🡒
        □((X ⋏ □(∼a) ⋏ (∼a)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := by
      have g₁ : ofAxioms 𝔸 ⊢ (X ⋏ (FormulaFinset.boxNeg (insert a N)).conj 🡒 (insert a N).disj) 🡒
          (X ⋏ (FormulaFinset.boxNeg (insert a N)).conj ⋏ ∼a 🡒 N.disj) := by cl_prover [h₃];
      have g₂ : ofAxioms 𝔸 ⊢ (X ⋏ □(∼a) ⋏ (∼a)) ⋏ (FormulaFinset.boxNeg N).conj 🡒
          X ⋏ (FormulaFinset.boxNeg (insert a N)).conj ⋏ ∼a := by cl_prover [h₂];
      exact box_mono (by cl_prover [g₁, g₂]);
    have h₅ : ofAxioms 𝔸 ⊢ (X ⋏ a) ▷ a := rhd_of_provable (by cl_prover);
    have h₆ : ofAxioms 𝔸 ⊢ (X ⋏ ∼□(∼a)) ▷ a :=
      (rhd_trans_left (rhd_of_provable (B := ∼□(∼a)) (by cl_prover)) ⨀ axiomJ5);
    have h₇ : ofAxioms 𝔸 ⊢ X 🡒 ((X ⋏ a) ⋎ (X ⋏ ∼□(∼a))) ⋎ (X ⋏ □(∼a) ⋏ (∼a)) := by
      cl_prover;
    have k₁ : ofAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 (X ⋏ a) ▷ Y := by
      cl_prover [h₁, rhd_trans_left h₅];
    have k₂ : ofAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 (X ⋏ ∼□(∼a)) ▷ Y := by
      cl_prover [h₁, rhd_trans_left h₆];
    have k₃ : ofAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒
        □(X ⋏ (FormulaFinset.boxNeg (insert a N)).conj 🡒 (insert a N).disj) 🡒
        (X ⋏ □(∼a) ⋏ (∼a)) ▷ Y := by
      cl_prover [h₁, h₄, ih (X ⋏ □(∼a) ⋏ (∼a))];
    cl_prover [k₁, k₂, k₃, rhd_of_cases (Y := Y) h₇];

private lemma box_conj_self : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := by
  have h : ofAxioms 𝔸 ⊢ □Γ.conj ⋏ □Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := box_and;
  cl_prover [h, box_conj (𝔸 := 𝔸) (Γ := Γ), box_conj_box (𝔸 := 𝔸) (Γ := Γ)];

private lemma boxNeg_eq_box :
    FormulaFinset.boxNeg N = (FormulaFinset.box (N.image Formula.neg)) := by
  rw [FormulaFinset.boxNeg, FormulaFinset.box, Finset.image_image];
  rfl;

private lemma conj_boxNeg_imp_box :
    ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □N.boxNeg.conj := by
  rw [boxNeg_eq_box];
  exact box_conj_box;

private lemma conj_boxNeg_imp_box_conj_neg :
    ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □(N.image Formula.neg).conj := by
  rw [boxNeg_eq_box];
  exact box_conj;

private lemma conj_neg_imp_neg_disj : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼N.disj := by
  have : ofAxioms 𝔸 ⊢ N.disj 🡒 ∼(N.image Formula.neg).conj := by
    apply left_Fdisj_intro;
    intro n hn;
    have : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼n :=
      left_Fconj_intro (Finset.mem_image_of_mem _ hn);
    cl_prover [this];
  cl_prover [this];

private lemma conj_witness_ant {D : Formula α} :
    ofAxioms 𝔸 ⊢ D ⋏ □(∼D) ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
      (witness Γ N D).ant.conj := by
  apply right_Fconj_intro;
  intro B hB;
  simp only [witness, Finset.mem_insert, Finset.mem_union] at hB;
  rcases hB with rfl | rfl | (hB | hB) | hB;
  · cl_prover;
  · cl_prover;
  · have : ofAxioms 𝔸 ⊢ Γ.conj 🡒 B := left_Fconj_intro hB;
    cl_prover [this];
  · have : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 B := left_Fconj_intro hB;
    cl_prover [this];
  · have : ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 B := left_Fconj_intro hB;
    cl_prover [this];

private lemma rhd_of_witness {D : Formula α}
    (h : ofAxioms 𝔸 ⊢ (witness Γ N D).ant.conj 🡒 (witness Γ N D).suc.disj) (Y : Formula α) :
    ofAxioms 𝔸 ⊢ Γ.box.conj ⋏ (N.image (· ▷ Y)).conj 🡒 D ▷ Y := by
  have h₁ : ofAxioms 𝔸 ⊢ D ⋏ □(∼D) ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
      N.disj := C_trans conj_witness_ant h;
  have h₂' : ofAxioms 𝔸 ⊢ (Γ.conj ⋏ Γ.box.conj) 🡒
      ((D ⋏ □(∼D)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := by cl_prover [h₁];
  have h₃ := box_mono h₂';
  have h₄ : ofAxioms 𝔸 ⊢ D ▷ (D ⋏ □(∼D)) ⋏ (D ⋏ □(∼D)) ▷ Y 🡒 D ▷ Y := axiomJ2;
  cl_prover [h₃, h₄, box_conj_self (𝔸 := 𝔸) (Γ := Γ),
    rhd_of_box_imp (𝔸 := 𝔸) N (D ⋏ □(∼D)) Y, rhd_and_box_neg (𝔸 := 𝔸) (A := D)];

private lemma conj_rhd_bot_imp_boxNeg :
    ofAxioms 𝔸 ⊢ (N.image (· ▷ ⊥)).conj 🡒 (FormulaFinset.boxNeg N).conj := by
  apply right_Fconj_intro;
  intro B hB;
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hB;
  exact C_trans (left_Fconj_intro (Finset.mem_image_of_mem _ hn)) rhd_bot;

private lemma conj_union_imp {Δ : FormulaFinset α} :
    ofAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj := by
  have h₁ : ofAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj := CFConjFConj_of_subset Finset.subset_union_left;
  have h₂ : ofAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Δ.conj := CFConjFConj_of_subset Finset.subset_union_right;
  cl_prover [h₁, h₂];

/-- The formulas `n ▷ Y` for the antecedents `n` of the pairs of `l` and the members `n` of `M`
follow from `□Γ` and the formulas of `l`, given the premises of the modal rules for `l`. -/
private lemma conj_rhd_of_premises {M : FormulaFinset α} {Y : Formula α}
    (hM : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 (M.image (· ▷ Y)).conj) :
    ∀ l : List (Formula α × Formula α),
      (∀ l₁ p l₂, l = l₁ ++ p :: l₂ → ofAxioms 𝔸 ⊢
        (witness Γ (M ∪ antecedents l₂) p.2).ant.conj 🡒
          (witness Γ (M ∪ antecedents l₂) p.2).suc.disj) →
      ofAxioms 𝔸 ⊢ Γ.box.conj ⋏ (rhdFormulas l).conj 🡒 ((M ∪ antecedents l).image (· ▷ Y)).conj
  | [], _ => by
    simp only [antecedents_nil, Finset.union_empty];
    cl_prover [hM];
  | (C, D) :: l, h => by
    have ih := conj_rhd_of_premises hM l fun l₁ p l₂ e ↦ h ((C, D) :: l₁) p l₂ (by simp [e]);
    have hD := rhd_of_witness (h [] (C, D) l rfl) Y;
    have h₁ : ofAxioms 𝔸 ⊢ (insert (C ▷ D) (rhdFormulas l)).conj 🡒
        C ▷ D ⋏ (rhdFormulas l).conj := CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ C ▷ D ⋏ D ▷ Y 🡒 C ▷ Y := axiomJ2;
    have h₃ : ofAxioms 𝔸 ⊢ C ▷ Y ⋏ ((M ∪ antecedents l).image (· ▷ Y)).conj 🡒
        (insert (C ▷ Y) ((M ∪ antecedents l).image (· ▷ Y))).conj := CKFConjinsertFConj;
    simp only [rhdFormulas_cons, antecedents_cons, Finset.union_insert, Finset.image_insert];
    cl_prover [ih, hD, h₁, h₂, h₃];

end IL.Gentzen

namespace Logic.IL

open Logic.ofAxioms IL.Gentzen

variable [DecidableEq α] {S : Sequent α}

lemma of_gentzen (h : ⊢ᴳ[𝐈𝐋] S) : 𝐈𝐋 ⊢ S.ant.conj 🡒 S.suc.disj := by
  induction h with
  | axm A => simp;
  | botL => simp only [Finset.conj_singleton]; exact efq;
  | wkL _ hΓ ih => exact C_trans (CFConjFConj_of_subset hΓ) ih;
  | wkR _ hΔ ih =>
    exact C_trans ih <| left_Fdisj_intro _ fun B hB ↦ right_Fdisj_intro _ (hΔ hB);
  | @impL Γ Δ A B _ _ ih₁ ih₂ =>
    have h₁ : 𝐈𝐋 ⊢ (insert (A 🡒 B) Γ).conj 🡒 (A 🡒 B) ⋏ Γ.conj := CinsertFConjKFConj;
    have h₂ : 𝐈𝐋 ⊢ (insert A Δ).disj 🡒 A ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : 𝐈𝐋 ⊢ B ⋏ Γ.conj 🡒 (insert B Γ).conj := CKFConjinsertFConj;
    cl_prover [ih₁, ih₂, h₁, h₂, h₃];
  | @impR Γ Δ A B _ ih =>
    have h₁ : 𝐈𝐋 ⊢ A ⋏ Γ.conj 🡒 (insert A Γ).conj := CKFConjinsertFConj;
    have h₂ : 𝐈𝐋 ⊢ (insert B Δ).disj 🡒 B ⋎ Δ.disj := CinsertFDisjAFDisj;
    have h₃ : 𝐈𝐋 ⊢ (A 🡒 B) ⋎ Δ.disj 🡒 (insert (A 🡒 B) Δ).disj := CAFDisjinsertFDisj;
    cl_prover [ih, h₁, h₂, h₃];
  | @rhd Γ l A B _ _ ih ihA =>
    have hB : 𝐈𝐋 ⊢ Γ.box.conj 🡒 (({B} : FormulaFinset α).image (· ▷ B)).conj := by
      simp only [Finset.image_singleton, Finset.conj_singleton];
      exact C_of_conseq (rhd_of_provable C_id);
    have h₁ := conj_rhd_of_premises hB l (by simpa [← Finset.insert_eq] using ih);
    have h₂ := rhd_of_witness ihA B;
    have h₃ : 𝐈𝐋 ⊢ (Γ.box ∪ rhdFormulas l).conj 🡒 Γ.box.conj ⋏ (rhdFormulas l).conj :=
      conj_union_imp;
    rw [← Finset.insert_eq] at h₁;
    simp only [Finset.disj_singleton];
    cl_prover [h₁, h₂, h₃];
  | @box Γ l B _ _ ih ihB =>
    have h₀ : 𝐈𝐋 ⊢ Γ.box.conj 🡒 ((∅ : FormulaFinset α).image (· ▷ ⊥)).conj := by
      simp only [Finset.image_empty, Finset.conj_empty];
      exact C_of_conseq Entailment.verum;
    have h₁ := conj_rhd_of_premises h₀ l (by simpa using ih);
    simp only [Finset.empty_union] at h₁;
    set N := antecedents l;
    have h₂ : 𝐈𝐋 ⊢ □B ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
        (insert (□B) (Γ ∪ Γ.box ∪ FormulaFinset.boxNeg N)).conj := by
      apply right_Fconj_intro;
      intro C hC;
      simp only [Finset.mem_insert, Finset.mem_union] at hC;
      rcases hC with rfl | (hC | hC) | hC;
      · cl_prover;
      · have : 𝐈𝐋 ⊢ Γ.conj 🡒 C := left_Fconj_intro hC;
        cl_prover [this];
      · have : 𝐈𝐋 ⊢ Γ.box.conj 🡒 C := left_Fconj_intro hC;
        cl_prover [this];
      · have : 𝐈𝐋 ⊢ (FormulaFinset.boxNeg N).conj 🡒 C := left_Fconj_intro hC;
        cl_prover [this];
    have h₃ : 𝐈𝐋 ⊢ (insert B N).disj 🡒 B ⋎ N.disj := CinsertFDisjAFDisj;
    have h₄ : 𝐈𝐋 ⊢ ((Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj) ⋏
        (N.image Formula.neg).conj 🡒 (□B 🡒 B) := by
      cl_prover [ihB, h₂, h₃, conj_neg_imp_neg_disj (𝔸 := ∅) (N := N)];
    have h₅ := box_mono h₄;
    have h₆ : 𝐈𝐋 ⊢ □((Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj) ⋏
        □(N.image Formula.neg).conj 🡒
        □(((Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj) ⋏
          (N.image Formula.neg).conj) := box_and;
    have h₇ : 𝐈𝐋 ⊢ □(Γ.conj ⋏ Γ.box.conj) ⋏ □(FormulaFinset.boxNeg N).conj 🡒
        □((Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj) := box_and;
    have h₈ : 𝐈𝐋 ⊢ □(□B 🡒 B) 🡒 □B := axiomL;
    have h₉ : 𝐈𝐋 ⊢ (Γ.box ∪ rhdFormulas l).conj 🡒 Γ.box.conj ⋏ (rhdFormulas l).conj :=
      conj_union_imp;
    simp only [Finset.disj_singleton];
    cl_prover [h₁, h₅, h₆, h₇, h₈, h₉, conj_rhd_bot_imp_boxNeg (𝔸 := ∅) (N := N),
      box_conj_self (𝔸 := ∅) (Γ := Γ), conj_boxNeg_imp_box (𝔸 := ∅) (N := N),
      conj_boxNeg_imp_box_conj_neg (𝔸 := ∅) (N := N)];

end Logic.IL

end FFL.InterpretabilityLogic

end
