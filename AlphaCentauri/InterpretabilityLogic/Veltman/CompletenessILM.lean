module

public import AlphaCentauri.InterpretabilityLogic.Veltman.Completeness
public import AlphaCentauri.InterpretabilityLogic.Veltman.Extension

/-!
# Completeness of $\mathbf{ILM}$ with respect to finite Veltman models

Finite adequate sets closed under conjoining an antecedent or consequent of a `▷`-formula with
`□`-formulas, up to the relation that each of the two formulas implies the other or its
possibility; a finite Veltman model satisfying the frame condition of $\mathbf{M}$ whose worlds are
maximal consistent subsets of such a set, and the completeness of $\mathbf{ILM}$.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*} [DecidableEq α]

/-! ### Subformulas of conjunctions -/

lemma Formula.exists_mem_subformulas_of_mem_conj₂ {A : Formula α} :
    {l : List (Formula α)} → A ∈ (⋀l).subformulas → (∀ B C, A ≠ B 🡒 C) → A ≠ ⊥ →
      ∃ B ∈ l, A ∈ B.subformulas
  | [], h, himp, hbot => by
    simp only [List.conj₂_nil] at h;
    change A ∈ insert (⊥ 🡒 ⊥) _ at h;
    simp_all [subformulas];
  | [B], h, _, _ => ⟨B, by simp, h⟩
  | B :: C :: l, h, himp, hbot => by
    change A ∈ insert _ _ at h;
    simp only [subformulas, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h;
    rcases h with h | (h | h | h | h | h) | h;
    all_goals first
      | exact (himp _ _ h).elim
      | exact (hbot h).elim
      | exact ⟨B, by simp, h⟩
      | obtain ⟨D, hD, h⟩ := exists_mem_subformulas_of_mem_conj₂ (l := C :: l) h himp hbot;
        exact ⟨D, by simp_all, h⟩

/-! ### Lemmas of $\mathbf{GL}$ -/

namespace Logic

variable {L : Logic α} [L.ExtendsGL] [Entailment.Cl L] {A B H : Formula α}
  {X Y : Finset (Formula α)}

omit [DecidableEq α] in
lemma or_dia_and_box_neg : L ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A)) := by
  change L ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ∼□(∼(A ⋏ □(∼A)));
  have h₁ : L ⊢ □(□(∼A) 🡒 ∼A) 🡒 □(∼A) := ExtendsGL.axiomL;
  have h₂ : L ⊢ □(∼(A ⋏ □(∼A))) 🡒 □(□(∼A) 🡒 ∼A) := box_mono <| by cl_prover;
  cl_prover [h₁, h₂];

omit [DecidableEq α] in
lemma dia_mono (h : L ⊢ A 🡒 B) : L ⊢ ◇A 🡒 ◇B := by
  have : L ⊢ □(∼B) 🡒 □(∼A) := box_mono <| by cl_prover [h];
  change L ⊢ ∼□(∼A) 🡒 ∼□(∼B);
  cl_prover [this];

lemma box_iff_conj_image_box : L ⊢ □X.conj 🡘 (X.image (□·)).conj := by
  apply E_intro;
  · apply right_Fconj_intro;
    simp only [Finset.mem_image, forall_exists_index, and_imp];
    rintro _ B hB rfl;
    exact box_mono <| left_Fconj_intro hB;
  · apply FConj_DT.mpr;
    have h : ((X.image (□·) : Finset (Formula α)) : Set (Formula α)) *⊢[L] □X.toList.conj := by
      apply box_conj_of_forall;
      intro B hB;
      exact Context.by_axm <| by simpa using hB;
    exact Context.of (box_mono <| K_right EConj₂Conj) ⨀ h;

lemma conj_imp_box_conj (hX : ∀ B ∈ X, ∃ C, B = □C) : L ⊢ X.conj 🡒 □X.conj := by
  apply C_trans _ <| K_right box_iff_conj_image_box;
  apply right_Fconj_intro;
  simp only [Finset.mem_image, forall_exists_index, and_imp];
  rintro _ B hB rfl;
  obtain ⟨C, rfl⟩ := hX B hB;
  exact C_trans (left_Fconj_intro hB) axiom4;

omit [DecidableEq α] in
lemma box_neg_iff_of_box (h : L ⊢ □A 🡒 (B 🡘 H)) : L ⊢ □A 🡒 (□(∼B) 🡘 □(∼H)) := by
  have h₁ : L ⊢ □□A 🡒 □(∼B 🡒 ∼H) := box_mono <| by cl_prover [h];
  have h₂ : L ⊢ □□A 🡒 □(∼H 🡒 ∼B) := box_mono <| by cl_prover [h];
  have h₃ : L ⊢ □(∼B 🡒 ∼H) 🡒 □(∼B) 🡒 □(∼H) := ExtendsGL.axiomK;
  have h₄ : L ⊢ □(∼H 🡒 ∼B) 🡒 □(∼H) 🡒 □(∼B) := ExtendsGL.axiomK;
  have h₅ : L ⊢ □A 🡒 □□A := axiom4;
  cl_prover [h₁, h₂, h₃, h₄, h₅];

omit [L.ExtendsGL] in
lemma exists_conj_iff (h : ∀ B ∈ X, L ⊢ H 🡒 B ∨ ∃ C ∈ Y, L ⊢ H 🡒 (B 🡘 C)) :
    ∃ X' ⊆ Y, L ⊢ H 🡒 (X.conj 🡘 X'.conj) := by
  induction X using Finset.induction_on with
  | empty =>
    use ∅;
    and_intros;
    · exact Finset.empty_subset _;
    · cl_prover;
  | @insert B X hB ih =>
    obtain ⟨X₀, hX₀, h₀⟩ := ih fun C hC ↦ h C (Finset.mem_insert_of_mem hC);
    have c₁ : L ⊢ (insert B X).conj 🡒 B ⋏ X.conj := CinsertFConjKFConj;
    have c₂ : L ⊢ B ⋏ X.conj 🡒 (insert B X).conj := CKFConjinsertFConj;
    rcases h B (Finset.mem_insert_self _ _) with h₁ | ⟨C, hC, h₁⟩;
    · use X₀;
      and_intros;
      · exact hX₀;
      · cl_prover [c₁, c₂, h₀, h₁];
    · use insert C X₀;
      and_intros;
      · exact Finset.insert_subset hC hX₀;
      · have c₃ : L ⊢ (insert C X₀).conj 🡒 C ⋏ X₀.conj := CinsertFConjKFConj;
        have c₄ : L ⊢ C ⋏ X₀.conj 🡒 (insert C X₀).conj := CKFConjinsertFConj;
        have h₂ : L ⊢ H 🡒 B 🡒 C := by cl_prover [h₁];
        have h₃ : L ⊢ H 🡒 C 🡒 B := by cl_prover [h₁];
        have h₄ : L ⊢ H 🡒 X.conj 🡒 X₀.conj := by cl_prover [h₀];
        have h₅ : L ⊢ H 🡒 X₀.conj 🡒 X.conj := by cl_prover [h₀];
        have d₁ : L ⊢ H 🡒 (insert B X).conj 🡒 (insert C X₀).conj := by cl_prover [c₁, c₄, h₂, h₄];
        have d₂ : L ⊢ H 🡒 (insert C X₀).conj 🡒 (insert B X).conj := by cl_prover [c₂, c₃, h₃, h₅];
        cl_prover [d₁, d₂];

lemma imp_or_dia_of_box_neg_imp_iff (hX : ∀ B ∈ X, ∃ C, B = □C)
    (h : L ⊢ □(∼A) 🡒 (X.conj 🡘 Y.conj)) : L ⊢ A ⋏ X.conj 🡒 (A ⋏ Y.conj) ⋎ ◇(A ⋏ Y.conj) := by
  have h₁ : L ⊢ A ⋏ X.conj 🡒
      ((A ⋏ X.conj) ⋏ □(∼(A ⋏ X.conj))) ⋎ ◇((A ⋏ X.conj) ⋏ □(∼(A ⋏ X.conj))) :=
    or_dia_and_box_neg;
  have h₂ : L ⊢ X.conj 🡒 □X.conj := conj_imp_box_conj hX;
  have h₃ : L ⊢ □(X.conj 🡒 ∼(A ⋏ X.conj) 🡒 ∼A) := provable_box <| by cl_prover;
  have h₄ : L ⊢ □(X.conj 🡒 ∼(A ⋏ X.conj) 🡒 ∼A) 🡒 □X.conj 🡒 □(∼(A ⋏ X.conj) 🡒 ∼A) :=
    ExtendsGL.axiomK;
  have h₅ : L ⊢ □(∼(A ⋏ X.conj) 🡒 ∼A) 🡒 □(∼(A ⋏ X.conj)) 🡒 □(∼A) := ExtendsGL.axiomK;
  have h₆ : L ⊢ (A ⋏ X.conj) ⋏ □(∼(A ⋏ X.conj)) 🡒 A ⋏ Y.conj := by
    cl_prover [h, h₂, h₃, h₄, h₅];
  have h₇ := dia_mono h₆;
  cl_prover [h₁, h₆, h₇];

end Logic

/-! ### Adequate sets for $\mathbf{ILM}$ -/

lemma Adequate.subformulas_subset {Φ : Finset (Formula α)} [Adequate Φ] {A : Formula α}
    (h : A ∈ Φ) : A.subformulas ⊆ Φ := by
  induction A with
  | atom a => simpa [subformulas] using h;
  | falsum => simpa [subformulas] using h;
  | imp A B ihA ihB =>
    simp only [subformulas, Finset.insert_subset_iff, Finset.union_subset_iff];
    exact ⟨h, ihA (Adequate.imp_left h), ihB (Adequate.imp_right h)⟩;
  | box A ih =>
    simp only [subformulas, Finset.insert_subset_iff];
    exact ⟨h, ih (Adequate.box h)⟩;
  | rhd A B ihA ihB =>
    simp only [subformulas, Finset.insert_subset_iff, Finset.union_subset_iff];
    exact ⟨h, ihA (Adequate.rhd_left h), ihB (Adequate.rhd_right h)⟩;

/-- `Φ` is adequate, and for every antecedent or consequent `B` of a `▷`-formula in `Φ` and every
finite set `X` of `□`-formulas in `Φ`, some antecedent or consequent `B'` of a `▷`-formula in `Φ`
satisfies `B ⋏ X.conj 🡒 B' ⋎ ◇B'` and `B' 🡒 (B ⋏ X.conj) ⋎ ◇(B ⋏ X.conj)` in $\mathbf{IL}$.

- [dJV90, Definition 6.1]
-/
class MAdequate (Φ : Finset (Formula α)) : Prop extends Adequate Φ where
  exists_isRhdOperand {B : Formula α} {X : Finset (Formula α)} : IsRhdOperand Φ B →
    (∀ C ∈ X, C ∈ Φ ∧ ∃ D, C = □D) → ∃ B', IsRhdOperand Φ B' ∧
      𝐈𝐋 ⊢ B ⋏ X.conj 🡒 B' ⋎ ◇B' ∧ 𝐈𝐋 ⊢ B' 🡒 (B ⋏ X.conj) ⋎ ◇(B ⋏ X.conj)

namespace mAdequateClosure

variable (Φ : Finset (Formula α))

open Classical in
/-- The antecedents and consequents of `▷`-formulas in `Φ`. -/
noncomputable def rhdOperands : Finset (Formula α) := Φ.filter (IsRhdOperand Φ)

open Classical in
/-- The `□`-formulas in `Φ`. -/
noncomputable def boxes : Finset (Formula α) := Φ.filter fun A ↦ ∃ B, A = □B

/-- The formulas `B ⋏ X.conj` with `B ∈ O` and `X` a set of formulas each of which is in
`boxes Φ` or is `□∼C` for some `C ∈ tree Φ (O.erase B)`. -/
noncomputable def tree (O : Finset (Formula α)) : Finset (Formula α) :=
  O.attach.biUnion fun B ↦
    ((boxes Φ ∪ (tree (O.erase B.1)).image fun C ↦ □(∼C)).powerset).image fun X ↦ B.1 ⋏ X.conj
termination_by O.card
decreasing_by exact Finset.card_erase_lt_of_mem B.2

variable {Φ} {O O' : Finset (Formula α)} {A B C : Formula α}

lemma mem_rhdOperands : A ∈ rhdOperands Φ ↔ A ∈ Φ ∧ IsRhdOperand Φ A := by
  classical
  simp [rhdOperands];

lemma mem_boxes : A ∈ boxes Φ ↔ A ∈ Φ ∧ ∃ B, A = □B := by
  classical
  simp [boxes];

lemma mem_tree : A ∈ tree Φ O ↔ ∃ B ∈ O, ∃ X ⊆ boxes Φ ∪ (tree Φ (O.erase B)).image (fun C ↦ □(∼C)),
    A = B ⋏ X.conj := by
  rw [tree];
  simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image,
    Finset.mem_powerset, Subtype.exists];
  grind;

lemma tree_mono (h : O ⊆ O') : tree Φ O ⊆ tree Φ O' := by
  induction hn : O.card using Nat.strong_induction_on generalizing O O' with
  | _ n ih =>
    intro A hA;
    obtain ⟨B, hB, X, hX, rfl⟩ := mem_tree.mp hA;
    apply mem_tree.mpr;
    use B;
    and_intros;
    · exact h hB;
    · use X;
      and_intros;
      · apply hX.trans;
        apply Finset.union_subset_union (subset_refl _);
        apply Finset.image_subset_image;
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hB) (Finset.erase_subset_erase B h) rfl;
      · rfl;

lemma exists_tree_erase (hA : A ∈ tree Φ O) :
    𝐈𝐋 ⊢ A 🡒 B ∨ ∃ A' ∈ tree Φ (O.erase B), 𝐈𝐋 ⊢ □(∼B) 🡒 (A 🡘 A') := by
  induction hn : O.card using Nat.strong_induction_on generalizing O A with
  | _ n ih =>
    obtain ⟨B', hB', X, hX, rfl⟩ := mem_tree.mp hA;
    by_cases hB : B' = B;
    · subst hB;
      exact .inl and₁;
    right;
    have h : ∀ C ∈ X, 𝐈𝐋 ⊢ □(∼B) 🡒 C ∨ ∃ C' ∈ boxes Φ ∪
        (tree Φ ((O.erase B').erase B)).image (fun C ↦ □(∼C)), 𝐈𝐋 ⊢ □(∼B) 🡒 (C 🡘 C') := by
      intro C hC;
      rcases Finset.mem_union.mp (hX hC) with hC | hC;
      · exact .inr ⟨C, Finset.mem_union_left _ hC, by cl_prover⟩;
      · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC;
        rcases ih _ (hn ▸ Finset.card_erase_lt_of_mem hB') hD rfl with h | ⟨D', hD', h⟩;
        · exact .inl <| Logic.box_mono <| by cl_prover [h];
        · exact .inr ⟨□(∼D'), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hD'),
            Logic.box_neg_iff_of_box h⟩;
    obtain ⟨X', hX', h⟩ := Logic.exists_conj_iff h;
    use B' ⋏ X'.conj;
    and_intros;
    · apply mem_tree.mpr;
      use B';
      and_intros;
      · exact Finset.mem_erase.mpr ⟨hB, hB'⟩;
      · use X';
        and_intros;
        · simpa [Finset.erase_right_comm] using hX';
        · rfl;
    · cl_prover [h];

variable [Adequate Φ]

private lemma mem_subformulas_and_conj {X : Finset (Formula α)}
    (h : B ∈ (A ⋏ X.conj).subformulas) (himp : ∀ C D, B ≠ C 🡒 D) (hbot : B ≠ ⊥) :
    B ∈ A.subformulas ∨ ∃ C ∈ X, B ∈ C.subformulas := by
  obtain ⟨C, hC, hBC⟩ := exists_mem_subformulas_of_mem_conj₂ (l := [A, X.conj]) h himp hbot;
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC;
  rcases hC with rfl | rfl;
  · exact .inl hBC;
  · obtain ⟨D, hD, hBD⟩ := exists_mem_subformulas_of_mem_conj₂ hBC himp hbot;
    exact .inr ⟨D, by simpa using hD, hBD⟩;

lemma mem_of_mem_tree (hO : O ⊆ rhdOperands Φ) (hA : A ∈ tree Φ O) (hB : B ∈ A.subformulas)
    (hB' : (∃ C D, B = C ▷ D) ∨ ∃ C, B = □C) :
    B ∈ Φ ∨ ∃ D ∈ tree Φ (rhdOperands Φ), B = □(∼D) := by
  induction hn : O.card using Nat.strong_induction_on generalizing O A with
  | _ n ih =>
    obtain ⟨b, hb, X, hX, rfl⟩ := mem_tree.mp hA;
    have himp : ∀ C D, B ≠ C 🡒 D := by
      rintro C D rfl;
      simp at hB';
    have hbot : B ≠ ⊥ := by
      rintro rfl;
      simp at hB';
    rcases mem_subformulas_and_conj hB himp hbot with hB | ⟨C, hC, hB⟩;
    · exact .inl <| Adequate.subformulas_subset (mem_rhdOperands.mp (hO hb)).1 hB;
    · rcases Finset.mem_union.mp (hX hC) with hC | hC;
      · exact .inl <| Adequate.subformulas_subset (mem_boxes.mp hC).1 hB;
      · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC;
        simp only [subformulas, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hB;
        rcases hB with rfl | rfl | hB | rfl;
        · exact .inr ⟨D, tree_mono ((Finset.erase_subset _ _).trans hO) hD, rfl⟩;
        · exact (himp _ _ rfl).elim;
        · exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hb) ((Finset.erase_subset _ _).trans hO) hD
            hB rfl;
        · exact (hbot rfl).elim;

end mAdequateClosure

end FFL.InterpretabilityLogic

end
