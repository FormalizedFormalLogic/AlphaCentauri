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

private lemma exists_box_of_subset {Y : Finset (Formula α)}
    (hY : Y ⊆ boxes Φ ∪ (tree Φ O).image fun C ↦ □(∼C)) : ∀ C ∈ Y, ∃ D, C = □D := by
  intro C hC;
  rcases Finset.mem_union.mp (hY hC) with hC | hC;
  · exact (mem_boxes.mp hC).2;
  · obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hC;
    exact ⟨_, rfl⟩;

lemma exists_tree_of_conj {X : Finset (Formula α)} (hB : B ∈ O)
    (hX : X ⊆ boxes Φ ∪ (tree Φ O).image fun C ↦ □(∼C)) :
    ∃ A ∈ tree Φ O, 𝐈𝐋 ⊢ B ⋏ X.conj 🡒 A ⋎ ◇A ∧ 𝐈𝐋 ⊢ A 🡒 (B ⋏ X.conj) ⋎ ◇(B ⋏ X.conj) := by
  have h : ∀ C ∈ X, 𝐈𝐋 ⊢ □(∼B) 🡒 C ∨ ∃ C' ∈ boxes Φ ∪
      (tree Φ (O.erase B)).image (fun C ↦ □(∼C)), 𝐈𝐋 ⊢ □(∼B) 🡒 (C 🡘 C') := by
    intro C hC;
    rcases Finset.mem_union.mp (hX hC) with hC | hC;
    · exact .inr ⟨C, Finset.mem_union_left _ hC, by cl_prover⟩;
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC;
      rcases exists_tree_erase (B := B) hD with h | ⟨D', hD', h⟩;
      · exact .inl <| Logic.box_mono <| by cl_prover [h];
      · exact .inr ⟨□(∼D'), Finset.mem_union_right _ (Finset.mem_image_of_mem _ hD'),
          Logic.box_neg_iff_of_box h⟩;
  obtain ⟨X', hX', h⟩ := Logic.exists_conj_iff h;
  use B ⋏ X'.conj;
  and_intros;
  · apply mem_tree.mpr;
    use B;
    and_intros;
    · exact hB;
    · use X';
  · exact Logic.imp_or_dia_of_box_neg_imp_iff (exists_box_of_subset hX) h;
  · exact Logic.imp_or_dia_of_box_neg_imp_iff (exists_box_of_subset hX') <| by cl_prover [h];

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

open mAdequateClosure in
/-- The antecedents and consequents of `▷`-formulas in `Φ` together with the trees over them. -/
noncomputable def mAdequateClosure.operands (Φ : Finset (Formula α)) : Finset (Formula α) :=
  rhdOperands Φ ∪ tree Φ (rhdOperands Φ)

open mAdequateClosure in
/-- The subformulas of the formulas in `Φ`, of `□∼A` for the trees `A` over `Φ`, and of `A ▷ B` for
`A` and `B` in `operands Φ`. -/
noncomputable def mAdequateClosure (Φ : Finset (Formula α)) : Finset (Formula α) :=
  (Φ ∪ (tree Φ (rhdOperands Φ)).image (fun A ↦ □(∼A)) ∪
    (operands Φ ×ˢ operands Φ).image (fun p ↦ p.1 ▷ p.2)).biUnion subformulas

namespace mAdequateClosure

variable {Φ : Finset (Formula α)} {A B C D : Formula α}

private lemma mem_iff : A ∈ mAdequateClosure Φ ↔
    (∃ B ∈ Φ, A ∈ B.subformulas) ∨ (∃ B ∈ tree Φ (rhdOperands Φ), A ∈ (□(∼B)).subformulas) ∨
      ∃ B ∈ operands Φ, ∃ C ∈ operands Φ, A ∈ (B ▷ C).subformulas := by
  simp only [mAdequateClosure, Finset.mem_biUnion, Finset.mem_union, Finset.mem_image,
    Finset.mem_product, Prod.exists];
  grind;

lemma subset : Φ ⊆ mAdequateClosure Φ := fun A hA ↦ mem_iff.mpr <| .inl ⟨A, hA, by simp⟩

lemma mem_of_mem_subformulas (hA : A ∈ mAdequateClosure Φ) (hB : B ∈ A.subformulas) :
    B ∈ mAdequateClosure Φ := by
  rcases mem_iff.mp hA with ⟨C, hC, h⟩ | ⟨C, hC, h⟩ | ⟨C, hC, D, hD, h⟩;
  · exact mem_iff.mpr <| .inl ⟨C, hC, subformulas_subset_of_mem h hB⟩;
  · exact mem_iff.mpr <| .inr <| .inl ⟨C, hC, subformulas_subset_of_mem h hB⟩;
  · exact mem_iff.mpr <| .inr <| .inr ⟨C, hC, D, hD, subformulas_subset_of_mem h hB⟩;

lemma rhd_mem (hA : A ∈ operands Φ) (hB : B ∈ operands Φ) : A ▷ B ∈ mAdequateClosure Φ :=
  mem_iff.mpr <| .inr <| .inr ⟨A, hA, B, hB, by simp⟩

variable [Adequate Φ]

private lemma mem_of_mem_operands (hA : A ∈ operands Φ) (hB : B ∈ A.subformulas)
    (hB' : (∃ C D, B = C ▷ D) ∨ ∃ C, B = □C) :
    B ∈ Φ ∨ ∃ D ∈ tree Φ (rhdOperands Φ), B = □(∼D) := by
  rcases Finset.mem_union.mp hA with hA | hA;
  · exact .inl <| Adequate.subformulas_subset (mem_rhdOperands.mp hA).1 hB;
  · exact mem_of_mem_tree (subset_refl _) hA hB hB';

lemma operands_of_rhd_mem (h : A ▷ B ∈ mAdequateClosure Φ) : A ∈ operands Φ ∧ B ∈ operands Φ := by
  have hΦ (h : A ▷ B ∈ Φ) : A ∈ operands Φ ∧ B ∈ operands Φ :=
    ⟨Finset.mem_union_left _ <| mem_rhdOperands.mpr ⟨Adequate.rhd_left h, .of_rhd_left h⟩,
      Finset.mem_union_left _ <| mem_rhdOperands.mpr ⟨Adequate.rhd_right h, .of_rhd_right h⟩⟩;
  have hΦ' (h : A ▷ B ∈ Φ ∨ ∃ D ∈ tree Φ (rhdOperands Φ), A ▷ B = □(∼D)) :
      A ∈ operands Φ ∧ B ∈ operands Φ := by
    rcases h with h | ⟨_, _, h⟩;
    · exact hΦ h;
    · simp at h;
  rcases mem_iff.mp h with ⟨C, hC, h⟩ | ⟨C, hC, h⟩ | ⟨C, hC, D, hD, h⟩;
  · exact hΦ <| Adequate.subformulas_subset hC h;
  · simp only [subformulas, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h;
    rcases h with h | h | h | h;
    · simp at h;
    · simp at h;
    · exact hΦ' <| mem_of_mem_tree (subset_refl _) hC h (.inl ⟨A, B, rfl⟩);
    · simp at h;
  · simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with h | h | h;
    · obtain ⟨rfl, rfl⟩ := rhd_inj.mp h;
      exact ⟨hC, hD⟩;
    · exact hΦ' <| mem_of_mem_operands hC h (.inl ⟨A, B, rfl⟩);
    · exact hΦ' <| mem_of_mem_operands hD h (.inl ⟨A, B, rfl⟩);

lemma isRhdOperand_iff : IsRhdOperand (mAdequateClosure Φ) A ↔ A ∈ operands Φ := by
  constructor;
  · rintro ⟨B, h | h⟩;
    · exact (operands_of_rhd_mem h).1;
    · exact (operands_of_rhd_mem h).2;
  · intro h;
    exact .of_rhd_left <| rhd_mem h h;

lemma box_mem (h : □A ∈ mAdequateClosure Φ) :
    □A ∈ boxes Φ ∨ ∃ D ∈ tree Φ (rhdOperands Φ), □A = □(∼D) := by
  have hΦ' (h : □A ∈ Φ ∨ ∃ D ∈ tree Φ (rhdOperands Φ), □A = □(∼D)) :
      □A ∈ boxes Φ ∨ ∃ D ∈ tree Φ (rhdOperands Φ), □A = □(∼D) := by
    rcases h with h | h;
    · exact .inl <| mem_boxes.mpr ⟨h, A, rfl⟩;
    · exact .inr h;
  rcases mem_iff.mp h with ⟨C, hC, h⟩ | ⟨C, hC, h⟩ | ⟨C, hC, D, hD, h⟩;
  · exact hΦ' <| .inl <| Adequate.subformulas_subset hC h;
  · simp only [subformulas, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at h;
    rcases h with h | h | h | h;
    · exact .inr ⟨C, hC, h⟩;
    · simp at h;
    · exact hΦ' <| mem_of_mem_tree (subset_refl _) hC h (.inr ⟨A, rfl⟩);
    · simp at h;
  · simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with h | h | h;
    · simp at h;
    · exact hΦ' <| mem_of_mem_operands hC h (.inr ⟨A, rfl⟩);
    · exact hΦ' <| mem_of_mem_operands hD h (.inr ⟨A, rfl⟩);

instance : Adequate (mAdequateClosure Φ) where
  imp_left h := mem_of_mem_subformulas h <| by simp [subformulas]
  imp_right h := mem_of_mem_subformulas h <| by simp [subformulas]
  box h := mem_of_mem_subformulas h <| by simp [subformulas]
  rhd_left h := mem_of_mem_subformulas h <| by simp [subformulas]
  rhd_right h := mem_of_mem_subformulas h <| by simp [subformulas]
  bot_rhd_bot := subset Adequate.bot_rhd_bot
  rhd_mem hA hB := rhd_mem (isRhdOperand_iff.mp hA) (isRhdOperand_iff.mp hB)
  box_neg_mem {A} hA := by
    rcases Finset.mem_union.mp (isRhdOperand_iff.mp hA) with hA | hA;
    · exact subset <| Adequate.box_neg_mem (mem_rhdOperands.mp hA).2;
    · exact mem_iff.mpr <| .inr <| .inl ⟨A, hA, by simp⟩;

instance : MAdequate (mAdequateClosure Φ) where
  exists_isRhdOperand {B X} hB hX := by
    have hX' : X ⊆ boxes Φ ∪ (tree Φ (rhdOperands Φ)).image fun C ↦ □(∼C) := by
      intro C hC;
      obtain ⟨hC, D, rfl⟩ := hX C hC;
      rcases box_mem hC with h | h;
      · exact Finset.mem_union_left _ h;
      · obtain ⟨E, hE, h⟩ := h;
        exact Finset.mem_union_right _ <| Finset.mem_image.mpr ⟨E, hE, h.symm⟩;
    rcases Finset.mem_union.mp (isRhdOperand_iff.mp hB) with hB | hB;
    · obtain ⟨A, hA, h⟩ := exists_tree_of_conj hB hX';
      exact ⟨A, isRhdOperand_iff.mpr <| Finset.mem_union_right _ hA, h⟩;
    · obtain ⟨b, hb, Y, hY, rfl⟩ := mem_tree.mp hB;
      have hY' : Y ∪ X ⊆ boxes Φ ∪ (tree Φ (rhdOperands Φ)).image fun C ↦ □(∼C) := by
        apply Finset.union_subset _ hX';
        apply hY.trans;
        apply Finset.union_subset_union (subset_refl _);
        exact Finset.image_subset_image <| tree_mono <| Finset.erase_subset _ _;
      obtain ⟨A, hA, h₁, h₂⟩ := exists_tree_of_conj hb hY';
      have c₁ : 𝐈𝐋 ⊢ (Y ∪ X).conj 🡒 Y.conj ⋏ X.conj := CFconjUnionKFconj;
      have c₂ : 𝐈𝐋 ⊢ Y.conj ⋏ X.conj 🡒 (Y ∪ X).conj := CKFconjFconjUnion;
      have c₃ : 𝐈𝐋 ⊢ ◇(b ⋏ (Y ∪ X).conj) 🡒 ◇((b ⋏ Y.conj) ⋏ X.conj) :=
        Logic.dia_mono <| by cl_prover [c₁];
      refine ⟨A, isRhdOperand_iff.mpr <| Finset.mem_union_right _ hA, ?_, ?_⟩;
      · cl_prover [c₂, h₁];
      · cl_prover [c₁, h₂, c₃];

end mAdequateClosure

/-! ### Critical successors containing the `□`-formulas of another -/

namespace MaximalConsistentSet

open Logic.ofAxioms

variable {Φ : Finset (Formula α)} [MAdequate Φ] {Γ Δ : MaximalConsistentSet 𝐈𝐋𝐌 Φ}
  {B C E : Formula α}

/-- - [dJV90, Theorem 6.3] -/
lemma CriticalSuccessor.exists_criticalSuccessor_box_subset (hE : IsRhdOperand Φ E)
    (hBC : B ▷ C ∈ Γ) (hΔ : CriticalSuccessor E Γ Δ) (hB : B ∈ Δ) :
    ∃ Θ, CriticalSuccessor E Γ Θ ∧ C ∈ Θ ∧ ∀ {D}, □D ∈ Δ → □D ∈ Θ := by
  let H := Γ.rhdDisj E;
  let P := (Δ.prebox.image (□·)).conj;
  let Y : Set (Formula α) := insert (∼H) <| insert (□(∼H)) <| insert C <| insert P <|
    {A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ};
  have hP {D} (hD : □D ∈ Δ) : 𝐈𝐋𝐌 ⊢ P 🡒 □D :=
    left_Fconj_intro <| Finset.mem_image_of_mem _ <| mem_prebox.mpr hD;
  have hY : Y *⊬[𝐈𝐋𝐌] ⊥ := by
    intro h;
    have h₁ : ({A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ}) *⊢[𝐈𝐋𝐌] C ⋏ P 🡒 H ⋎ ∼□(∼H) := by
      have := Context.deduct <| Context.deduct <| Context.deduct <| Context.deduct h;
      cl_prover [this];
    have h₂ : Γ.literals *⊢[𝐈𝐋𝐌] □(C ⋏ P 🡒 H ⋎ ◇H) := by
      apply Context.weakening _ (Logic.box_of_provable h₁);
      rintro _ ⟨A, hA, rfl⟩;
      exact mem_literals hA;
    have h₃ : Γ.literals *⊢[𝐈𝐋𝐌] H ▷ E := by
      apply fdisj_rhd;
      intro G hG;
      exact Context.by_axm <| mem_literals (Finset.mem_filter.mp hG).2;
    have h₄ : Γ.literals *⊢[𝐈𝐋𝐌] (H ⋎ ◇H) ▷ H := Context.of or_dia_rhd;
    have h₅ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) <| axiomJ1 (A := C ⋏ P) (B := H ⋎ ◇H);
    have h₆ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) <| axiomJ2 (A := C ⋏ P) (B := H ⋎ ◇H) (C := H);
    have h₇ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) <| axiomJ2 (A := C ⋏ P) (B := H) (C := E);
    have h₈ : Γ.literals *⊢[𝐈𝐋𝐌] (C ⋏ P) ▷ E := by cl_prover [h₂, h₃, h₄, h₅, h₆, h₇];
    have h₉ : 𝐈𝐋𝐌 ⊢ □Δ.prebox.conj 🡘 P := Logic.box_iff_conj_image_box;
    have h₁₀ : Γ.literals *⊢[𝐈𝐋𝐌] (B ⋏ P) ▷ (C ⋏ P) := by
      have i₁ : 𝐈𝐋𝐌 ⊢ B ▷ C 🡒 (B ⋏ □Δ.prebox.conj) ▷ (C ⋏ □Δ.prebox.conj) := Logic.ILM.axiomM;
      have i₂ : 𝐈𝐋𝐌 ⊢ (B ⋏ □Δ.prebox.conj) ▷ (C ⋏ □Δ.prebox.conj) 🡒 (B ⋏ P) ▷ (C ⋏ □Δ.prebox.conj) :=
        rhd_anti_left <| by cl_prover [h₉];
      have i₃ : 𝐈𝐋𝐌 ⊢ (B ⋏ P) ▷ (C ⋏ □Δ.prebox.conj) 🡒 (B ⋏ P) ▷ (C ⋏ P) :=
        rhd_mono_right <| by cl_prover [h₉];
      exact Context.of (C_trans i₁ <| C_trans i₂ i₃) ⨀ Context.by_axm (mem_literals hBC);
    have h₁₁ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) <| axiomJ2 (A := B ⋏ P) (B := C ⋏ P) (C := E);
    have h₁₂ : Γ.literals *⊢[𝐈𝐋𝐌] (B ⋏ P) ▷ E := by cl_prover [h₈, h₁₀, h₁₁];
    obtain ⟨B', hB', i₁, i₂⟩ := MAdequate.exists_isRhdOperand (Φ := Φ)
      (IsRhdOperand.of_rhd_left (mem_of_mem hBC)) (X := Δ.prebox.image (□·)) <| by
        intro D hD;
        obtain ⟨D, hD', rfl⟩ := Finset.mem_image.mp hD;
        exact ⟨mem_of_mem (mem_prebox.mp hD'), D, rfl⟩;
    replace i₁ : 𝐈𝐋𝐌 ⊢ B ⋏ P 🡒 B' ⋎ ◇B' := IL_subset i₁;
    replace i₂ : 𝐈𝐋𝐌 ⊢ B' 🡒 (B ⋏ P) ⋎ ◇(B ⋏ P) := IL_subset i₂;
    have h₁₃ : Γ.literals *⊢[𝐈𝐋𝐌] B' ▷ E := by
      have j₁ : 𝐈𝐋𝐌 ⊢ B' ▷ ((B ⋏ P) ⋎ ◇(B ⋏ P)) := rhd_of_provable i₂;
      have j₂ : 𝐈𝐋𝐌 ⊢ ((B ⋏ P) ⋎ ◇(B ⋏ P)) ▷ (B ⋏ P) := or_dia_rhd;
      have j₃ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) <|
        axiomJ2 (A := B') (B := (B ⋏ P) ⋎ ◇(B ⋏ P)) (C := B ⋏ P);
      have j₄ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) <| axiomJ2 (A := B') (B := B ⋏ P) (C := E);
      have j₅ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) j₁;
      have j₆ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Γ.literals) j₂;
      cl_prover [h₁₂, j₃, j₄, j₅, j₆];
    have h₁₄ : B' ▷ E ∈ Γ := (mem_iff_provable (Adequate.rhd_mem hB' hE)).mpr h₁₃;
    have h₁₅ : Δ.literals *⊢[𝐈𝐋𝐌] B ⋏ P := by
      have k₁ : 𝐈𝐋𝐌 ⊢ Δ.set.conj 🡒 P := CFConjFConj_of_subset <| by
        intro D hD;
        obtain ⟨D, hD', rfl⟩ := Finset.mem_image.mp hD;
        exact mem_prebox.mp hD';
      have k₂ : Δ.literals *⊢[𝐈𝐋𝐌] Δ.set.conj :=
        Context.weakening (fun _ h ↦ mem_literals h) <| FConj_DT.mp C_id;
      exact K_intro (Context.by_axm <| mem_literals hB) (Context.of k₁ ⨀ k₂);
    have h₁₆ : Δ.literals *⊢[𝐈𝐋𝐌] ∼B' :=
      provable_neg_of_not_mem hB'.mem (hΔ.not_mem h₁₄);
    have h₁₇ : Δ.literals *⊢[𝐈𝐋𝐌] □(∼B') := Context.by_axm <| mem_literals (hΔ.box_neg_mem h₁₄);
    have h₁₈ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Δ.literals) i₁;
    exact consistent_literals <| by
      change Δ.literals *⊢[𝐈𝐋𝐌] ⊥;
      change Δ.literals *⊢[𝐈𝐋𝐌] B ⋏ P 🡒 B' ⋎ ∼□(∼B') at h₁₈;
      cl_prover [h₁₅, h₁₆, h₁₇, h₁₈];
  obtain ⟨Θ, hΘ⟩ := exists_consistent_union (Φ := Φ) hY;
  have hm {A} (hA : A ∈ Φ) (h : Y *⊢[𝐈𝐋𝐌] A) : A ∈ Θ := mem_of_provable hΘ hA h;
  have hPY : Y *⊢[𝐈𝐋𝐌] P := Context.by_axm <| by simp [Y];
  have hb {D} (hD : □D ∈ Δ) : □D ∈ Θ := hm (mem_of_mem hD) <| Context.of (hP hD) ⨀ hPY;
  have hG {G} (hG : G ▷ E ∈ Γ) : G ∉ Θ ∧ □(∼G) ∈ Θ := by
    have h₁ : G ∈ Φ.filter (· ▷ E ∈ Γ) :=
      Finset.mem_filter.mpr ⟨Adequate.rhd_left (mem_of_mem hG), hG⟩;
    have h₂ : 𝐈𝐋𝐌 ⊢ G 🡒 H := right_Fdisj_intro _ h₁;
    have h₃ : 𝐈𝐋𝐌 ⊢ □(∼H) 🡒 □(∼G) := Logic.box_mono <| by cl_prover [h₂];
    have h₄ : Y *⊢[𝐈𝐋𝐌] ∼H := Context.by_axm <| by simp [Y];
    have h₅ : Y *⊢[𝐈𝐋𝐌] □(∼H) := Context.by_axm <| by simp [Y];
    constructor;
    · apply not_mem_of_provable_neg hΘ;
      have h₆ := Context.of (𝓢 := 𝐈𝐋𝐌) (Γ := Y) h₂;
      cl_prover [h₄, h₆];
    · exact hm (Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hG)) <| Context.of h₃ ⨀ h₅;
  obtain ⟨A, hA, hA'⟩ := hΔ.exists_box;
  use Θ;
  and_intros;
  · exact ⟨⟨fun h ↦ hm (Adequate.box (mem_of_mem h)) (Context.by_axm <| by simp [Y, h]),
      fun h ↦ hm (mem_of_mem h) (Context.by_axm <| by simp [Y, h]), A, hb hA, hA'⟩,
      fun h ↦ (hG h).1, fun h ↦ (hG h).2⟩;
  · exact hm (Adequate.rhd_right (mem_of_mem hBC)) (Context.by_axm <| by simp [Y]);
  · exact hb;

end MaximalConsistentSet

end FFL.InterpretabilityLogic

end
