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
        (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : ofAxioms 𝔸 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ofAxioms 𝔸 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

lemma box_conj_box : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.box.conj := by
  have h₁ : ofAxioms 𝔸 ⊢ Γ.box.conj 🡒 Γ.box.box.conj := by
    apply right_Fconj_intro;
    intro B hB;
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
    exact C_trans (left_Fconj_intro hC) axiom4;
  have h₂ : ofAxioms 𝔸 ⊢ Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
  cl_prover [h₁, h₂];

lemma rhd_of_box_imp (N : FormulaFinset α) (X Y : Formula α) :
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

lemma conj_boxNeg_imp_box : ofAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □N.boxNeg.conj := by
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
    have : ofAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼n :=
      left_Fconj_intro (Finset.mem_image_of_mem _ hn);
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
  have h₄ : ofAxioms 𝔸 ⊢ D ▷ (D ⋏ □(∼D)) ⋏ (D ⋏ □(∼D)) ▷ Y 🡒 D ▷ Y := axiomJ2;
  cl_prover [h₃, h₄, box_conj_self (𝔸 := 𝔸) (Γ := Γ),
    rhd_of_box_imp (𝔸 := 𝔸) N (D ⋏ □(∼D)) Y, rhd_self_conj (𝔸 := 𝔸) (D := D)];

lemma conj_rhd_bot_imp_boxNeg :
    ofAxioms 𝔸 ⊢ (N.image (· ▷ ⊥)).conj 🡒 (FormulaFinset.boxNeg N).conj := by
  apply right_Fconj_intro;
  intro B hB;
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hB;
  exact C_trans (left_Fconj_intro (Finset.mem_image_of_mem _ hn)) box_neg_of_rhd_bot;

lemma conj_union_imp {Δ : FormulaFinset α} : ofAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj := by
  have h₁ : ofAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj := CFConjFConj_of_subset Finset.subset_union_left;
  have h₂ : ofAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Δ.conj := CFConjFConj_of_subset Finset.subset_union_right;
  cl_prover [h₁, h₂];

/-- The formulas `n ▷ Y` for the antecedents `n` of the pairs of `l` and the members `n` of `M`
follow from `□Γ` and the formulas of `l`, given the premises of the modal rules for `l`. -/
lemma conj_rhd_of_premises {M : FormulaFinset α} {Y : Formula α}
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

end Logic.ofAxioms

namespace Logic.IL

open Logic.ofAxioms

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
      exact C_of_conseq (rhd_of_imp C_id);
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
