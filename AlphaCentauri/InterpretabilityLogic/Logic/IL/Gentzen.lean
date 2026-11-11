module

public import AlphaCentauri.InterpretabilityLogic.Gentzen.Veltman
public import AlphaCentauri.InterpretabilityLogic.Logic.IL.Basic

/-!
# The sequent calculus for $\mathbf{IL}$ and its Veltman semantics

A sequent derivable in the sequent calculus for $\mathbf{IL}$ has the implication from the
conjunction of its antecedent to the disjunction of its succedent derivable in $\mathbf{IL}$. The
calculus is sound for Veltman models, is complete for finite Veltman models, and agrees with
$\mathbf{IL}$ on them.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula IL

variable {α : Type*}

namespace IL.Gentzen

open Logic Logic.ofILAxioms

variable {𝔸 : FormulaSet α} {A B C D X Y : Formula α}

private lemma rhd_trans_left (h : ofILAxioms 𝔸 ⊢ A ▷ B) : ofILAxioms 𝔸 ⊢ B ▷ C 🡒 A ▷ C := by
  have : ofILAxioms 𝔸 ⊢ A ▷ B ⋏ B ▷ C 🡒 A ▷ C := axiomJ2;
  cl_prover [h, this];

private lemma rhd_of_cases {X₁ X₂ X₃ : Formula α} (h : ofILAxioms 𝔸 ⊢ X 🡒 (X₁ ⋎ X₂) ⋎ X₃) :
    ofILAxioms 𝔸 ⊢ X₁ ▷ Y 🡒 X₂ ▷ Y 🡒 X₃ ▷ Y 🡒 X ▷ Y := by
  have h₁ : ofILAxioms 𝔸 ⊢ X₁ ▷ Y ⋏ X₂ ▷ Y 🡒 (X₁ ⋎ X₂) ▷ Y := axiomJ3;
  have h₂ : ofILAxioms 𝔸 ⊢ (X₁ ⋎ X₂) ▷ Y ⋏ X₃ ▷ Y 🡒 ((X₁ ⋎ X₂) ⋎ X₃) ▷ Y := axiomJ3;
  cl_prover [rhd_anti_left (C := Y) h, h₁, h₂];

variable [DecidableEq α] {Γ N : FormulaFinset α}

private lemma box_conj : ofILAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.conj := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : ofILAxioms 𝔸 ⊢ (∅ : FormulaFinset α).conj := by simp [Finset.conj];
    exact C_of_conseq (nec this);
  | insert A Γ _ ih =>
    have h₁ : ofILAxioms 𝔸 ⊢
        (insert (□A) (FormulaFinset.box Γ)).conj 🡒 □A ⋏ (FormulaFinset.box Γ).conj :=
      CinsertFConjKFConj;
    have h₂ : ofILAxioms 𝔸 ⊢ □A ⋏ □Γ.conj 🡒 □(A ⋏ Γ.conj) := box_and;
    have h₃ : ofILAxioms 𝔸 ⊢ □(A ⋏ Γ.conj) 🡒 □(insert A Γ).conj := box_mono CKFConjinsertFConj;
    rw [FormulaFinset.box, Finset.image_insert];
    cl_prover [ih, h₁, h₂, h₃];

private lemma box_conj_box : ofILAxioms 𝔸 ⊢ Γ.box.conj 🡒 □Γ.box.conj := by
  have h₁ : ofILAxioms 𝔸 ⊢ Γ.box.conj 🡒 Γ.box.box.conj := by
    apply right_Fconj_intro;
    intro B hB;
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB;
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
    exact C_trans (left_Fconj_intro hC) axiom4;
  have h₂ : ofILAxioms 𝔸 ⊢ Γ.box.box.conj 🡒 □Γ.box.conj := box_conj;
  cl_prover [h₁, h₂];

private lemma rhd_of_box_imp (N : FormulaFinset α) (X Y : Formula α) :
    ofILAxioms 𝔸 ⊢
      (N.image (· ▷ Y)).conj 🡒 □(X ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) 🡒 X ▷ Y := by
  induction N using Finset.induction_on generalizing X with
  | empty =>
    have h : ofILAxioms 𝔸 ⊢ □(X ⋏ (FormulaFinset.boxNeg ∅).conj 🡒 (∅ : FormulaFinset α).disj)
        🡒 □(X 🡒 Y) := box_mono (by
          simp only [Finset.image_empty, Finset.conj_empty, Finset.disj_empty];
          cl_prover);
    have h' : ofILAxioms 𝔸 ⊢ □(X 🡒 Y) 🡒 X ▷ Y := axiomJ1;
    cl_prover [h, h'];
  | insert a N _ ih =>
    have h₁ : ofILAxioms 𝔸 ⊢
        ((insert a N).image (· ▷ Y)).conj 🡒 a ▷ Y ⋏ (N.image (· ▷ Y)).conj := by
      rw [Finset.image_insert];
      exact CinsertFConjKFConj;
    have h₂ : ofILAxioms 𝔸 ⊢
        □(∼a) ⋏ (FormulaFinset.boxNeg N).conj 🡒 (FormulaFinset.boxNeg (insert a N)).conj := by
      rw [FormulaFinset.boxNeg, FormulaFinset.boxNeg, Finset.image_insert];
      exact CKFConjinsertFConj;
    have h₃ : ofILAxioms 𝔸 ⊢ (insert a N).disj 🡒 a ⋎ N.disj := CinsertFDisjAFDisj;
    have h₄ : ofILAxioms 𝔸 ⊢ □(X ⋏ (FormulaFinset.boxNeg (insert a N)).conj 🡒 (insert a N).disj) 🡒
        □((X ⋏ □(∼a) ⋏ (∼a)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := by
      have g₁ : ofILAxioms 𝔸 ⊢ (X ⋏ (FormulaFinset.boxNeg (insert a N)).conj 🡒 (insert a N).disj) 🡒
          (X ⋏ (FormulaFinset.boxNeg (insert a N)).conj ⋏ ∼a 🡒 N.disj) := by cl_prover [h₃];
      have g₂ : ofILAxioms 𝔸 ⊢ (X ⋏ □(∼a) ⋏ (∼a)) ⋏ (FormulaFinset.boxNeg N).conj 🡒
          X ⋏ (FormulaFinset.boxNeg (insert a N)).conj ⋏ ∼a := by cl_prover [h₂];
      exact box_mono (by cl_prover [g₁, g₂]);
    have h₅ : ofILAxioms 𝔸 ⊢ (X ⋏ a) ▷ a := rhd_of_provable (by cl_prover);
    have h₆ : ofILAxioms 𝔸 ⊢ (X ⋏ ∼□(∼a)) ▷ a :=
      (rhd_trans_left (rhd_of_provable (B := ∼□(∼a)) (by cl_prover)) ⨀ axiomJ5);
    have h₇ : ofILAxioms 𝔸 ⊢ X 🡒 ((X ⋏ a) ⋎ (X ⋏ ∼□(∼a))) ⋎ (X ⋏ □(∼a) ⋏ (∼a)) := by
      cl_prover;
    have k₁ : ofILAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 (X ⋏ a) ▷ Y := by
      cl_prover [h₁, rhd_trans_left h₅];
    have k₂ : ofILAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒 (X ⋏ ∼□(∼a)) ▷ Y := by
      cl_prover [h₁, rhd_trans_left h₆];
    have k₃ : ofILAxioms 𝔸 ⊢ ((insert a N).image (· ▷ Y)).conj 🡒
        □(X ⋏ (FormulaFinset.boxNeg (insert a N)).conj 🡒 (insert a N).disj) 🡒
        (X ⋏ □(∼a) ⋏ (∼a)) ▷ Y := by
      cl_prover [h₁, h₄, ih (X ⋏ □(∼a) ⋏ (∼a))];
    cl_prover [k₁, k₂, k₃, rhd_of_cases (Y := Y) h₇];

private lemma box_conj_self : ofILAxioms 𝔸 ⊢ Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := by
  have h : ofILAxioms 𝔸 ⊢ □Γ.conj ⋏ □Γ.box.conj 🡒 □(Γ.conj ⋏ Γ.box.conj) := box_and;
  cl_prover [h, box_conj (𝔸 := 𝔸) (Γ := Γ), box_conj_box (𝔸 := 𝔸) (Γ := Γ)];

private lemma boxNeg_eq_box :
    FormulaFinset.boxNeg N = (FormulaFinset.box (N.image Formula.neg)) := by
  rw [FormulaFinset.boxNeg, FormulaFinset.box, Finset.image_image];
  rfl;

private lemma conj_boxNeg_imp_box :
    ofILAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □N.boxNeg.conj := by
  rw [boxNeg_eq_box];
  exact box_conj_box;

private lemma conj_boxNeg_imp_box_conj_neg :
    ofILAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 □(N.image Formula.neg).conj := by
  rw [boxNeg_eq_box];
  exact box_conj;

private lemma conj_neg_imp_neg_disj : ofILAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼N.disj := by
  have : ofILAxioms 𝔸 ⊢ N.disj 🡒 ∼(N.image Formula.neg).conj := by
    apply left_Fdisj_intro;
    intro n hn;
    have : ofILAxioms 𝔸 ⊢ (N.image Formula.neg).conj 🡒 ∼n :=
      left_Fconj_intro (Finset.mem_image_of_mem _ hn);
    cl_prover [this];
  cl_prover [this];

private lemma conj_witness_ant {D : Formula α} :
    ofILAxioms 𝔸 ⊢ D ⋏ □(∼D) ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
      (witness Γ N D).ant.conj := by
  apply right_Fconj_intro;
  intro B hB;
  simp only [witness, Finset.mem_insert, Finset.mem_union] at hB;
  rcases hB with rfl | rfl | (hB | hB) | hB;
  · cl_prover;
  · cl_prover;
  · have : ofILAxioms 𝔸 ⊢ Γ.conj 🡒 B := left_Fconj_intro hB;
    cl_prover [this];
  · have : ofILAxioms 𝔸 ⊢ Γ.box.conj 🡒 B := left_Fconj_intro hB;
    cl_prover [this];
  · have : ofILAxioms 𝔸 ⊢ (FormulaFinset.boxNeg N).conj 🡒 B := left_Fconj_intro hB;
    cl_prover [this];

private lemma rhd_of_witness {D : Formula α}
    (h : ofILAxioms 𝔸 ⊢ (witness Γ N D).ant.conj 🡒 (witness Γ N D).suc.disj) (Y : Formula α) :
    ofILAxioms 𝔸 ⊢ Γ.box.conj ⋏ (N.image (· ▷ Y)).conj 🡒 D ▷ Y := by
  have h₁ : ofILAxioms 𝔸 ⊢ D ⋏ □(∼D) ⋏ (Γ.conj ⋏ Γ.box.conj) ⋏ (FormulaFinset.boxNeg N).conj 🡒
      N.disj := C_trans conj_witness_ant h;
  have h₂' : ofILAxioms 𝔸 ⊢ (Γ.conj ⋏ Γ.box.conj) 🡒
      ((D ⋏ □(∼D)) ⋏ (FormulaFinset.boxNeg N).conj 🡒 N.disj) := by cl_prover [h₁];
  have h₃ := box_mono h₂';
  have h₄ : ofILAxioms 𝔸 ⊢ D ▷ (D ⋏ □(∼D)) ⋏ (D ⋏ □(∼D)) ▷ Y 🡒 D ▷ Y := axiomJ2;
  cl_prover [h₃, h₄, box_conj_self (𝔸 := 𝔸) (Γ := Γ),
    rhd_of_box_imp (𝔸 := 𝔸) N (D ⋏ □(∼D)) Y, rhd_and_box_neg (𝔸 := 𝔸) (A := D)];

private lemma conj_rhd_bot_imp_boxNeg :
    ofILAxioms 𝔸 ⊢ (N.image (· ▷ ⊥)).conj 🡒 (FormulaFinset.boxNeg N).conj := by
  apply right_Fconj_intro;
  intro B hB;
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hB;
  exact C_trans (left_Fconj_intro (Finset.mem_image_of_mem _ hn)) rhd_bot;

private lemma conj_union_imp {Δ : FormulaFinset α} :
    ofILAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj ⋏ Δ.conj := by
  have h₁ : ofILAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Γ.conj := CFConjFConj_of_subset Finset.subset_union_left;
  have h₂ : ofILAxioms 𝔸 ⊢ (Γ ∪ Δ).conj 🡒 Δ.conj := CFConjFConj_of_subset Finset.subset_union_right;
  cl_prover [h₁, h₂];

/-- The formulas `n ▷ Y` for the antecedents `n` of the pairs of `l` and the members `n` of `M`
follow from `□Γ` and the formulas of `l`, given the premises of the modal rules for `l`. -/
private lemma conj_rhd_of_premises {M : FormulaFinset α} {Y : Formula α}
    (hM : ofILAxioms 𝔸 ⊢ Γ.box.conj 🡒 (M.image (· ▷ Y)).conj) :
    ∀ l : List (Formula α × Formula α),
      (∀ l₁ p l₂, l = l₁ ++ p :: l₂ → ofILAxioms 𝔸 ⊢
        (witness Γ (M ∪ antecedents l₂) p.2).ant.conj 🡒
          (witness Γ (M ∪ antecedents l₂) p.2).suc.disj) →
      ofILAxioms 𝔸 ⊢ Γ.box.conj ⋏ (rhdFormulas l).conj 🡒 ((M ∪ antecedents l).image (· ▷ Y)).conj
  | [], _ => by
    simp only [antecedents_nil, Finset.union_empty];
    cl_prover [hM];
  | (C, D) :: l, h => by
    have ih := conj_rhd_of_premises hM l fun l₁ p l₂ e ↦ h ((C, D) :: l₁) p l₂ (by simp [e]);
    have hD := rhd_of_witness (h [] (C, D) l rfl) Y;
    have h₁ : ofILAxioms 𝔸 ⊢ (insert (C ▷ D) (rhdFormulas l)).conj 🡒
        C ▷ D ⋏ (rhdFormulas l).conj := CinsertFConjKFConj;
    have h₂ : ofILAxioms 𝔸 ⊢ C ▷ D ⋏ D ▷ Y 🡒 C ▷ Y := axiomJ2;
    have h₃ : ofILAxioms 𝔸 ⊢ C ▷ Y ⋏ ((M ∪ antecedents l).image (· ▷ Y)).conj 🡒
        (insert (C ▷ Y) ((M ∪ antecedents l).image (· ▷ Y))).conj := CKFConjinsertFConj;
    simp only [rhdFormulas_cons, antecedents_cons, Finset.union_insert, Finset.image_insert];
    cl_prover [ih, hD, h₁, h₂, h₃];

end IL.Gentzen

open Logic.ofILAxioms IL.Gentzen

namespace Logic.IL

variable {α : Type*} [DecidableEq α] {S : Sequent α}

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

namespace IL

open Veltman Veltman.Model Veltman.Model.World
open SaturatedSequent

namespace Gentzen

variable {α : Type} [DecidableEq α] {S : Sequent α}

theorem sound {κ : Type*} [Nonempty κ] (M : Veltman.Model κ α) [M.IsIL] (h : ⊢ᴳ[𝐈𝐋] S) :
    M.ValidatesSequent S := by
  intro x hx;
  exact forces_disj.mp <|
    Logic.ofILAxioms.sound (by simp) (Logic.IL.of_gentzen h) x (forces_conj.mpr hx);

theorem complete
    (h : ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [Finite κ] → [M.IsIL] →
      M.ValidatesSequent S) :
    ⊢ᴳ[𝐈𝐋] S := by
  by_contra hS;
  obtain ⟨x₀, hx₀⟩ := lindenbaum (BS := S) hS
    (fun _ hA ↦ subset_closure (Finset.mem_union_left _ hA))
    (fun _ hA ↦ subset_closure (Finset.mem_union_right _ hA));
  obtain ⟨B, hB, hw⟩ := h (countermodel x₀) (⟨[], trivial⟩ : Path x₀)
    (fun A hA ↦ countermodel.truthlemma.1 (hx₀.ant hA));
  exact countermodel.truthlemma.2 (hx₀.suc hB) hw;

end Gentzen

end IL

namespace Logic.IL


variable {α : Type} [DecidableEq α] {A : Formula α}

/-- - [dJV90, Theorem 4.1] -/
theorem gentzen_TFAE : [
    𝐈𝐋 ⊢ A,
    ⊢ᴳ[𝐈𝐋] ∅ ⟹ {A},
    ∀ {κ : Type} [Nonempty κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A,
    ∀ {κ : Type} [Nonempty κ] [Finite κ] (M : Veltman.Model κ α), [M.IsIL] → M ⊧ A
  ].TFAE := by
  tfae_have 1 → 3 := by
    intro h _ _ M _;
    exact Logic.ofILAxioms.sound (by simp) h;
  tfae_have 3 → 4 := by
    intro h _ _ _ M _;
    exact h M;
  tfae_have 4 → 2 := by
    intro h;
    apply IL.Gentzen.complete;
    intro _ _ M _ _ x _;
    use A;
    and_intros;
    · simp;
    · exact h M x;
  tfae_have 2 → 1 := by
    intro h;
    simpa using of_gentzen h ⨀ (by simp [Finset.conj]);
  tfae_finish;

end Logic.IL

end FFL.InterpretabilityLogic

end
