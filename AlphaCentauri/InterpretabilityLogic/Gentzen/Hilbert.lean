module

public import AlphaCentauri.InterpretabilityLogic.Gentzen.Basic
public import AlphaCentauri.InterpretabilityLogic.Logic

/-!
# Soundness of the sequent calculus for $\mathbf{IL}$ with respect to the Hilbert system

A sequent derivable in the sequent calculus for $\mathbf{IL}$ has the implication from the
conjunction of its antecedent to the disjunction of its succedent derivable in $\mathbf{IL}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula IL

variable {α : Type*}

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {A B C D X Y : Formula α}

lemma axiom4 : ofAxioms 𝔸 ⊢ □A 🡒 □□A := by
  have h₁ : ofAxioms 𝔸 ⊢ □(□A ⋏ A) 🡒 □A := box_mono (by cl_prover);
  have h₂ : ofAxioms 𝔸 ⊢ □(□A ⋏ A) 🡒 □□A := box_mono (by cl_prover);
  have h₃ : ofAxioms 𝔸 ⊢ A 🡒 □(□A ⋏ A) 🡒 □A ⋏ A := by cl_prover [h₁];
  have h₄ : ofAxioms 𝔸 ⊢ □(□(□A ⋏ A) 🡒 □A ⋏ A) 🡒 □(□A ⋏ A) := axiomL;
  cl_prover [box_mono h₃, h₂, h₄];

lemma box_and : ofAxioms 𝔸 ⊢ □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : ofAxioms 𝔸 ⊢ □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : ofAxioms 𝔸 ⊢ □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := axiomK;
  cl_prover [h₁, h₂];

lemma rhd_self_conj : ofAxioms 𝔸 ⊢ D ▷ (D ⋏ □(∼D)) := by
  have h₁ : ofAxioms 𝔸 ⊢ □(□(∼D) 🡒 ∼D) 🡒 □(∼D) := axiomL;
  have h₂ : ofAxioms 𝔸 ⊢ □(∼(D ⋏ □(∼D))) 🡒 □(□(∼D) 🡒 ∼D) := box_mono (by cl_prover);
  have h₃ : ofAxioms 𝔸 ⊢ D 🡒 (D ⋏ □(∼D)) ⋎ ∼□(∼(D ⋏ □(∼D))) := by cl_prover [h₁, h₂];
  have h₄ : ofAxioms 𝔸 ⊢ D ▷ ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) := axiomJ1 ⨀ nec h₃;
  have h₅ : ofAxioms 𝔸 ⊢ (D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) := axiomJ1 ⨀ nec (C_id (𝓢 := ofAxioms 𝔸));
  have h₆ : ofAxioms 𝔸 ⊢ ◇(D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) := axiomJ5;
  have h₇ : ofAxioms 𝔸 ⊢ (D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) ⋏ ◇(D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) 🡒
    ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) ▷ (D ⋏ □(∼D)) := axiomJ3;
  have h₈ : ofAxioms 𝔸 ⊢ D ▷ ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) ⋏
    ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) ▷ (D ⋏ □(∼D)) 🡒 D ▷ (D ⋏ □(∼D)) := axiomJ2;
  cl_prover [h₄, h₅, h₆, h₇, h₈];

lemma rhd_of_imp (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h

lemma rhd_trans_left (h : ofAxioms 𝔸 ⊢ A ▷ B) : ofAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have : ofAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h, this];

lemma rhd_of_cases {X₁ X₂ X₃ : Formula α} (h : ofAxioms 𝔸 ⊢ X 🡒 (X₁ ⋎ X₂) ⋎ X₃) :
    ofAxioms 𝔸 ⊢ X₁ ▷ Y 🡒 X₂ ▷ Y 🡒 X₃ ▷ Y 🡒 X ▷ Y := by
  have h₁ : ofAxioms 𝔸 ⊢ X₁ ▷ Y ⋏ X₂ ▷ Y 🡒 (X₁ ⋎ X₂) ▷ Y := axiomJ3;
  have h₂ : ofAxioms 𝔸 ⊢ (X₁ ⋎ X₂) ▷ Y ⋏ X₃ ▷ Y 🡒 ((X₁ ⋎ X₂) ⋎ X₃) ▷ Y := axiomJ3;
  cl_prover [rhd_anti_left (C := Y) h, h₁, h₂];

lemma box_neg_of_rhd_bot : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼A) := by
  have h₁ : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 ∼□(∼A) 🡒 ∼□(⊥ 🡒 ⊥) := axiomJ4;
  have h₂ : ofAxioms 𝔸 ⊢ □(⊥ 🡒 ⊥) := nec (C_id (𝓢 := ofAxioms 𝔸));
  cl_prover [h₁, h₂];

variable [DecidableEq α] {Γ N : FormulaFinset α}

lemma box_conj : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : ofAxioms 𝔸 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact C_of_conseq (nec this);
  | insert A Γ _ ih =>
    have h₁ : ofAxioms 𝔸 ⊢
        (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj := CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ofAxioms 𝔸 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

lemma box_conj_box : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.box.conj := by
  have h₁ : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 (FormulaFinset.box Γ.box).conj :=
    right_Fconj_intro _ _ fun B hB ↦ by
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
      exact C_trans (left_Fconj_intro hC) axiom4;
  have h₂ : ofAxioms 𝔸 ⊢ (FormulaFinset.box Γ.box).conj 🡒 □Γ.box.conj := box_conj;
  cl_prover [h₁, h₂];

lemma rhd_of_box_imp (N : FormulaFinset α) (X Y : Formula α) :
    ofAxioms 𝔸 ⊢ (N.image (· ▷ Y)).conj 🡒 □(X ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) 🡒 X ▷ Y := by
  induction N using Finset.induction_on generalizing X with
  | empty =>
    have h : ofAxioms 𝔸 ⊢ □(X ⋏ (FormulaFinset.boxNeg ∅).conj 🡒 (∅ : FormulaFinset α).disj)
        🡒 □(X 🡒 Y) := box_mono (by simp [Finset.conj, Finset.disj]; cl_prover);
    have h' : ofAxioms 𝔸 ⊢ □(X 🡒 Y) 🡒 X ▷ Y := axiomJ1;
    cl_prover [h, h'];
  | insert a N _ ih =>
    have h₁ : ofAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 a ▷ Y ⋏ (N.image (· ▷ Y)).conj := by
      rw [Finset.image_insert];
      exact CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ □(∼a) ⋏ (FormulaFinset.boxNeg N).conj 🡒 (FormulaFinset.boxNeg (insert a N)).conj := by
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
    have h₅ : ofAxioms 𝔸 ⊢ (X ⋏ a) ▷ a := rhd_of_imp (by cl_prover);
    have h₆ : ofAxioms 𝔸 ⊢ (X ⋏ ∼□(∼a)) ▷ a :=
      (rhd_trans_left (rhd_of_imp (B := ∼□(∼a)) (by cl_prover)) ⨀ axiomJ5);
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

lemma box_conj_self : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := by
  have h : ofAxioms 𝔸 ⊢ □Γ.conj ⋏ □Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := box_and;
  cl_prover [h, box_conj (𝔸 := 𝔸) (Γ := Γ), box_conj_box (𝔸 := 𝔸) (Γ := Γ)];

lemma boxNeg_eq_box : FormulaFinset.boxNeg N = (FormulaFinset.box (N.image Formula.neg)) := by
  rw [FormulaFinset.boxNeg, FormulaFinset.box, Finset.image_image];
  rfl;

lemma conj_boxNeg_imp_box : ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □(FormulaFinset.boxNeg N).conj := by
  rw [boxNeg_eq_box];
  exact box_conj_box;

lemma conj_boxNeg_imp_box_conj_neg :
    ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □(N.image Formula.neg).conj := by
  rw [boxNeg_eq_box];
  exact box_conj;

lemma conj_neg_imp_neg_disj : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼N.disj := by
  have : ofAxioms 𝔸 ⊢ N.disj 🡒 ∼(N.image Formula.neg).conj := by
    apply left_Fdisj_intro;
    intro n hn;
    have : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼n := left_Fconj_intro (Finset.mem_image_of_mem _ hn);
    cl_prover [this];
  cl_prover [this];

lemma conj_witness_ant {D : Formula α} :
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

lemma rhd_of_witness {D : Formula α}
    (h : ofAxioms 𝔸 ⊢ (witness Γ N D).ant.conj 🡒 (witness Γ N D).suc.disj) (Y : Formula α) :
    ofAxioms 𝔸 ⊢ Γ.box.conj ⋏ (N.image (· ▷ Y)).conj 🡒 D ▷ Y := by
  have h₁ : ofAxioms 𝔸 ⊢ D ⋏ □(∼D) ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
      N.disj := C_trans conj_witness_ant h;
  have h₂' : ofAxioms 𝔸 ⊢ (Γ.conj ⋏ Γ.box.conj) 🡒
      ((D ⋏ □(∼D)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := by cl_prover [h₁];
  have h₃ := box_mono h₂';
  have h₄ : ofAxioms 𝔸 ⊢ D ▷ ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) := axiomJ1 ⨀ nec h₃;
  have h₅ : ofAxioms 𝔸 ⊢ (D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) := axiomJ1 ⨀ nec (C_id (𝓢 := ofAxioms 𝔸));
  have h₆ : ofAxioms 𝔸 ⊢ ◇(D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) := axiomJ5;
  have h₇ : ofAxioms 𝔸 ⊢ (D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) ⋏ ◇(D ⋏ □(∼D)) ▷ (D ⋏ □(∼D)) 🡒
    ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) ▷ (D ⋏ □(∼D)) := axiomJ3;
  have h₈ : ofAxioms 𝔸 ⊢ D ▷ ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) ⋏
    ((D ⋏ □(∼D)) ⋎ ◇(D ⋏ □(∼D))) ▷ (D ⋏ □(∼D)) 🡒 D ▷ (D ⋏ □(∼D)) := axiomJ2;
  cl_prover [h₄, h₅, h₆, h₇, h₈];

lemma rhd_of_imp (h : ofAxioms 𝔸 ⊢ A 🡒 B) : ofAxioms 𝔸 ⊢ A ▷ B := axiomJ1 ⨀ nec h

lemma rhd_trans_left (h : ofAxioms 𝔸 ⊢ A ▷ B) : ofAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have : ofAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h, this];

lemma rhd_of_cases {X₁ X₂ X₃ : Formula α} (h : ofAxioms 𝔸 ⊢ X 🡒 (X₁ ⋎ X₂) ⋎ X₃) :
    ofAxioms 𝔸 ⊢ X₁ ▷ Y 🡒 X₂ ▷ Y 🡒 X₃ ▷ Y 🡒 X ▷ Y := by
  have h₁ : ofAxioms 𝔸 ⊢ X₁ ▷ Y ⋏ X₂ ▷ Y 🡒 (X₁ ⋎ X₂) ▷ Y := axiomJ3;
  have h₂ : ofAxioms 𝔸 ⊢ (X₁ ⋎ X₂) ▷ Y ⋏ X₃ ▷ Y 🡒 ((X₁ ⋎ X₂) ⋎ X₃) ▷ Y := axiomJ3;
  cl_prover [rhd_anti_left (C := Y) h, h₁, h₂];

lemma box_neg_of_rhd_bot : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼A) := by
  have h₁ : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 ∼□(∼A) 🡒 ∼□(⊥ 🡒 ⊥) := axiomJ4;
  have h₂ : ofAxioms 𝔸 ⊢ □(⊥ 🡒 ⊥) := nec (C_id (𝓢 := ofAxioms 𝔸));
  cl_prover [h₁, h₂];

variable [DecidableEq α] {Γ N : FormulaFinset α}

lemma box_conj : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : ofAxioms 𝔸 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact C_of_conseq (nec this);
  | insert A Γ _ ih =>
    have h₁ : ofAxioms 𝔸 ⊢
        (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj := CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ofAxioms 𝔸 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

lemma box_conj_box : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.box.conj := by
  have h₁ : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 (FormulaFinset.box Γ.box).conj :=
    right_Fconj_intro _ _ fun B hB ↦ by
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
      exact C_trans (left_Fconj_intro hC) axiom4;
  have h₂ : ofAxioms 𝔸 ⊢ (FormulaFinset.box Γ.box).conj 🡒 □Γ.box.conj := box_conj;
  cl_prover [h₁, h₂];

lemma rhd_of_box_imp (N : FormulaFinset α) (X Y : Formula α) :
    ofAxioms 𝔸 ⊢ (N.image (· ▷ Y)).conj 🡒 □(X ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) 🡒 X ▷ Y := by
  induction N using Finset.induction_on generalizing X with
  | empty =>
    have h : ofAxioms 𝔸 ⊢ □(X ⋏ (FormulaFinset.boxNeg ∅).conj 🡒 (∅ : FormulaFinset α).disj)
        🡒 □(X 🡒 Y) := box_mono (by simp [Finset.conj, Finset.disj]; cl_prover);
    have h' : ofAxioms 𝔸 ⊢ □(X 🡒 Y) 🡒 X ▷ Y := axiomJ1;
    cl_prover [h, h'];
  | insert a N _ ih =>
    have h₁ : ofAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 a ▷ Y ⋏ (N.image (· ▷ Y)).conj := by
      rw [Finset.image_insert];
      exact CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ □(∼a) ⋏ (FormulaFinset.boxNeg N).conj 🡒 (FormulaFinset.boxNeg (insert a N)).conj := by
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
    have h₅ : ofAxioms 𝔸 ⊢ (X ⋏ a) ▷ a := rhd_of_imp (by cl_prover);
    have h₆ : ofAxioms 𝔸 ⊢ (X ⋏ ∼□(∼a)) ▷ a :=
      (rhd_trans_left (rhd_of_imp (B := ∼□(∼a)) (by cl_prover)) ⨀ axiomJ5);
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

lemma box_conj_self : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := by
  have h : ofAxioms 𝔸 ⊢ □Γ.conj ⋏ □Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := box_and;
  cl_prover [h, box_conj (𝔸 := 𝔸) (Γ := Γ), box_conj_box (𝔸 := 𝔸) (Γ := Γ)];

lemma boxNeg_eq_box : FormulaFinset.boxNeg N = (FormulaFinset.box (N.image Formula.neg)) := by
  rw [FormulaFinset.boxNeg, FormulaFinset.box, Finset.image_image];
  rfl;

lemma conj_boxNeg_imp_box : ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □(FormulaFinset.boxNeg N).conj := by
  rw [boxNeg_eq_box];
  exact box_conj_box;

lemma conj_boxNeg_imp_box_conj_neg :
    ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □(N.image Formula.neg).conj := by
  rw [boxNeg_eq_box];
  exact box_conj;

lemma conj_neg_imp_neg_disj : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼N.disj := by
  have : ofAxioms 𝔸 ⊢ N.disj 🡒 ∼(N.image Formula.neg).conj := by
    apply left_Fdisj_intro;
    intro n hn;
    have : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼n := left_Fconj_intro (Finset.mem_image_of_mem _ hn);
    cl_prover [this];
  cl_prover [this];

lemma conj_witness_ant {D : Formula α} :
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

lemma rhd_of_witness {D : Formula α}
    (h : ofAxioms 𝔸 ⊢ (witness Γ N D).ant.conj 🡒 (witness Γ N D).suc.disj) (Y : Formula α) :
    ofAxioms 𝔸 ⊢ Γ.box.conj ⋏ (N.image (· ▷ Y)).conj 🡒 D ▷ Y := by
  have h₁ : ofAxioms 𝔸 ⊢ D ⋏ □(∼D) ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
      N.disj := C_trans conj_witness_ant h;
  have h₂' : ofAxioms 𝔸 ⊢ (Γ.conj ⋏ Γ.box.conj) 🡒
      ((D ⋏ □(∼D)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := by cl_prover [h₁];
  have h₂ := nec h₂';
  have h₃ : ofAxioms 𝔸 ⊢ □((Γ.conj ⋏ Γ.box.conj) 🡒
      ((D ⋏ □(∼D)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj)) 🡒 □(Γ.conj ⋏ Γ.box.conj) 🡒
      □((D ⋏ □(∼D)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := axiomK;
  have h₄ : ofAxioms 𝔸 ⊢ D ▷ (D ⋏ □(∼D)) ⋏ (D ⋏ □(∼D)) ▷ Y 🡒 D ▷ Y := axiomJ2;
  cl_prover [h₃, h₄, box_conj_self (𝔸 := 𝔸) (Γ := Γ),
    rhd_of_box_imp (𝔸 := 𝔸) N (D ⋏ □(∼D)) Y, rhd_self_conj (𝔸 := 𝔸) (D := D)];

end Logic.ofAxioms

end FFL.InterpretabilityLogic

end
