module

public import AlphaCentauri.InterpretabilityLogic.Logic.Basic

/-!
# Maximal consistent subsets of adequate sets

Finite adequate sets of formulas, the maximal consistent subsets of such a set relative to an
extension of $\mathbf{IL}$, and their (critical) successors. For extensions of $\mathbf{IL}^-$,
adequate sets in the sense of Kurahashi and Okawa, Ignatiev's successors, and the existence of
successors containing prescribed formulas.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*} [DecidableEq α]

/-! ### Adequate sets -/

/-- `A` is the antecedent or the consequent of some `▷`-formula in `Φ`. -/
def IsRhdOperand (Φ : Finset (Formula α)) (A : Formula α) : Prop := ∃ B, A ▷ B ∈ Φ ∨ B ▷ A ∈ Φ

/-- `Φ` is closed under subformulas, contains `⊥ ▷ ⊥`, and contains `A ▷ B` and `□(∼A)` for all
antecedents and consequents `A`, `B` of `▷`-formulas in `Φ`.

- [dJV90, Definition 3.1]
- [KO21, Definition 4.1]
-/
class Adequate (Φ : Finset (Formula α)) : Prop where
  imp_left {A B} : A 🡒 B ∈ Φ → A ∈ Φ
  imp_right {A B} : A 🡒 B ∈ Φ → B ∈ Φ
  box {A} : □A ∈ Φ → A ∈ Φ
  rhd_left {A B} : A ▷ B ∈ Φ → A ∈ Φ
  rhd_right {A B} : A ▷ B ∈ Φ → B ∈ Φ
  bot_rhd_bot : ⊥ ▷ ⊥ ∈ Φ
  rhd_mem {A B} : IsRhdOperand Φ A → IsRhdOperand Φ B → A ▷ B ∈ Φ
  box_neg_mem : ∀ {A}, IsRhdOperand Φ A → □(∼A) ∈ Φ

namespace IsRhdOperand

variable {Φ : Finset (Formula α)} {A B : Formula α}

lemma of_rhd_left (h : A ▷ B ∈ Φ) : IsRhdOperand Φ A := ⟨B, .inl h⟩

lemma of_rhd_right (h : A ▷ B ∈ Φ) : IsRhdOperand Φ B := ⟨A, .inr h⟩

variable [Adequate Φ]

lemma bot : IsRhdOperand Φ ⊥ := of_rhd_left Adequate.bot_rhd_bot

lemma mem (h : IsRhdOperand Φ A) : A ∈ Φ := by
  obtain ⟨B, h | h⟩ := h;
  · exact Adequate.rhd_left h;
  · exact Adequate.rhd_right h;

end IsRhdOperand

/-- A finite adequate set containing `S`. -/
def adequateClosure (S : Finset (Formula α)) : Finset (Formula α) :=
  let T := insert ⊥ (S.biUnion subformulas);
  T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪ T.image (fun A ↦ ∼A)

namespace adequateClosure

variable {S : Finset (Formula α)} {A B : Formula α}

private lemma subset_of_mem (h : A ∈ insert ⊥ (S.biUnion subformulas)) :
    A.subformulas ⊆ insert ⊥ (S.biUnion subformulas) := by
  simp only [Finset.mem_insert, Finset.mem_biUnion] at h;
  rcases h with rfl | ⟨C, hC, h⟩;
  · simp [subformulas];
  · exact (subformulas_subset_of_mem h).trans <|
      (Finset.subset_biUnion_of_mem _ hC).trans (Finset.subset_insert _ _);

private lemma mem_iff : A ∈ adequateClosure S ↔
    A ∈ insert ⊥ (S.biUnion subformulas) ∨
    (∃ B C, B ∈ insert ⊥ (S.biUnion subformulas) ∧ C ∈ insert ⊥ (S.biUnion subformulas) ∧
      B ▷ C = A) ∨
    (∃ B ∈ insert ⊥ (S.biUnion subformulas), □(∼B) = A) ∨
    (∃ B ∈ insert ⊥ (S.biUnion subformulas), ∼B = A) := by
  simp only [adequateClosure, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists,
    and_assoc, or_assoc];

lemma subset : S ⊆ adequateClosure S := by
  intro A hA;
  apply mem_iff.mpr <| Or.inl _;
  simp only [Finset.mem_insert, Finset.mem_biUnion];
  exact .inr ⟨A, hA, mem_subformulas_self⟩

private lemma sub (h₁ : A ∈ insert ⊥ (S.biUnion subformulas)) (h₂ : B ∈ A.subformulas) :
    B ∈ adequateClosure S := mem_iff.mpr <| .inl <| subset_of_mem h₁ h₂

private lemma isRhdOperand (h : IsRhdOperand (adequateClosure S) A) :
    A ∈ insert ⊥ (S.biUnion subformulas) := by
  obtain ⟨B, h | h⟩ := h <;> rcases mem_iff.mp h with h | ⟨_, _, h₁, h₂, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩;
  · exact subset_of_mem h <| by simp [subformulas];
  · grind;
  · simp at h;
  · simp at h;
  · exact subset_of_mem h <| by simp [subformulas];
  · grind;
  · simp at h;
  · simp at h;

instance : Adequate (adequateClosure S) where
  imp_left h := by
    rcases mem_iff.mp h with h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h₁, h⟩;
    · exact sub h <| by simp [subformulas];
    · simp at h;
    · simp at h;
    · obtain ⟨rfl, -⟩ := imp_inj.mp h;
      exact mem_iff.mpr <| .inl h₁;
  imp_right h := by
    rcases mem_iff.mp h with h | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩;
    · exact sub h <| by simp [subformulas];
    · simp at h;
    · simp at h;
    · obtain ⟨-, rfl⟩ := imp_inj.mp h;
      exact mem_iff.mpr <| .inl <| Finset.mem_insert_self _ _;
  box h := by
    rcases mem_iff.mp h with h | ⟨_, _, _, _, h⟩ | ⟨B, h₁, h⟩ | ⟨_, _, h⟩;
    · exact sub h <| by simp [subformulas];
    · simp at h;
    · obtain rfl := box_inj.mp h;
      exact mem_iff.mpr <| .inr <| .inr <| .inr ⟨B, h₁, rfl⟩;
    · simp at h;
  rhd_left h := by
    rcases mem_iff.mp h with h | ⟨_, _, h₁, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩;
    · exact sub h <| by simp [subformulas];
    · obtain ⟨rfl, -⟩ := rhd_inj.mp h;
      exact mem_iff.mpr <| .inl h₁;
    · simp at h;
    · simp at h;
  rhd_right h := by
    rcases mem_iff.mp h with h | ⟨_, _, _, h₁, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩;
    · exact sub h <| by simp [subformulas];
    · obtain ⟨-, rfl⟩ := rhd_inj.mp h;
      exact mem_iff.mpr <| .inl h₁;
    · simp at h;
    · simp at h;
  bot_rhd_bot := mem_iff.mpr <| .inr <| .inl ⟨⊥, ⊥, by simp, by simp, rfl⟩
  rhd_mem hA hB := mem_iff.mpr <| .inr <| .inl ⟨_, _, isRhdOperand hA, isRhdOperand hB, rfl⟩
  box_neg_mem hA := mem_iff.mpr <| .inr <| .inr <| .inl ⟨_, isRhdOperand hA, rfl⟩

end adequateClosure

/-! ### Maximal consistent sets -/

/-- A subset `Γ` of `Φ` such that `Γ`, together with the negations of the formulas in `Φ` outside
`Γ`, is consistent in `L`. -/
structure MaximalConsistentSet (L : Logic α) (Φ : Finset (Formula α)) where
  set : Finset (Formula α)
  subset : set ⊆ Φ
  consistent : (↑set ∪ (∼·) '' ↑(Φ \ set)) *⊬[L] ⊥

namespace MaximalConsistentSet

open Logic

variable {L : Logic α} {Φ : Finset (Formula α)} {X : FormulaSet α}
  {A B C D E F : Formula α}

section

variable {Γ : MaximalConsistentSet L Φ}

instance : Membership (Formula α) (MaximalConsistentSet L Φ) := ⟨fun Γ A ↦ A ∈ Γ.set⟩

lemma mem_def : A ∈ Γ ↔ A ∈ Γ.set := Iff.rfl

instance : DecidablePred (· ∈ Γ) := fun A ↦ inferInstanceAs (Decidable (A ∈ Γ.set))

lemma ext {Γ Δ : MaximalConsistentSet L Φ} (h : Γ.set = Δ.set) : Γ = Δ := by
  cases Γ; cases Δ; simp_all;

instance : Finite (MaximalConsistentSet L Φ) :=
  Finite.of_injective (β := Φ.powerset) (fun Γ ↦ ⟨Γ.set, Finset.mem_powerset.mpr Γ.subset⟩)
    fun _ _ h ↦ ext <| by simpa using h

lemma mem_of_mem (h : A ∈ Γ) : A ∈ Φ := Γ.subset h

/-- The formulas of `Γ` together with the negations of the formulas in `Φ` outside `Γ`. -/
def literals (Γ : MaximalConsistentSet L Φ) : FormulaSet α := ↑Γ.set ∪ (∼·) '' ↑(Φ \ Γ.set)

lemma mem_literals (h : A ∈ Γ) : A ∈ Γ.literals := .inl h

lemma neg_mem_literals (hA : A ∈ Φ) (h : A ∉ Γ) : ∼A ∈ Γ.literals :=
  .inr ⟨A, by simpa using ⟨hA, h⟩, rfl⟩

lemma consistent_literals : Γ.literals *⊬[L] ⊥ := Γ.consistent

variable [Entailment.Cl L]

lemma mem_of_provable (hX : (X ∪ Γ.literals) *⊬[L] ⊥) (hA : A ∈ Φ)
    (h : X *⊢[L] A) : A ∈ Γ := by
  by_contra hn;
  apply hX;
  have h₁ : (X ∪ Γ.literals) *⊢[L] A := Context.weakening Set.subset_union_left h;
  have h₂ : (X ∪ Γ.literals) *⊢[L] ∼A :=
    Context.by_axm <| .inr <| neg_mem_literals hA hn;
  cl_prover [h₁, h₂];

lemma not_mem_of_provable_neg (hX : (X ∪ Γ.literals) *⊬[L] ⊥)
    (h : X *⊢[L] ∼A) : A ∉ Γ := by
  intro hm;
  apply hX;
  have h₁ : (X ∪ Γ.literals) *⊢[L] ∼A := Context.weakening Set.subset_union_left h;
  have h₂ : (X ∪ Γ.literals) *⊢[L] A := Context.by_axm <| .inr <| mem_literals hm;
  cl_prover [h₁, h₂];

lemma mem_iff_provable (hA : A ∈ Φ) : A ∈ Γ ↔ Γ.literals *⊢[L] A :=
  ⟨fun h ↦ Context.by_axm <| mem_literals h,
    mem_of_provable (by simpa using consistent_literals) hA⟩

lemma provable_neg_of_not_mem (hA : A ∈ Φ) (h : A ∉ Γ) : Γ.literals *⊢[L] ∼A :=
  Context.by_axm <| neg_mem_literals hA h

lemma bot_not_mem : ⊥ ∉ Γ := fun h ↦ consistent_literals <| Context.by_axm <| mem_literals h

lemma imp_mem_iff (h : A 🡒 B ∈ Φ) (hA : A ∈ Φ) (hB : B ∈ Φ) :
    A 🡒 B ∈ Γ ↔ (A ∈ Γ → B ∈ Γ) := by
  constructor;
  · intro h₁ h₂;
    exact (mem_iff_provable hB).mpr <|
      ((mem_iff_provable h).mp h₁) ⨀ ((mem_iff_provable hA).mp h₂);
  · intro h₁;
    apply (mem_iff_provable h).mpr;
    by_cases h₂ : A ∈ Γ;
    · exact C_of_conseq <| (mem_iff_provable hB).mp (h₁ h₂);
    · have := provable_neg_of_not_mem hA h₂;
      cl_prover [this];

lemma not_mem_of_neg_mem (h : ∼A ∈ Γ) : A ∉ Γ := fun h₁ ↦
  consistent_literals <| Context.by_axm (mem_literals h) ⨀ Context.by_axm (mem_literals h₁)

/-! ### Lindenbaum's lemma -/

private lemma exists_consistent_aux (h : X *⊬[L] ⊥) (S : Finset (Formula α)) :
    ∃ T ⊆ S, (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊬[L] ⊥ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simpa using h⟩;
  | @insert a S ha ih =>
    obtain ⟨T, hT, hY⟩ := ih;
    by_cases h₁ : insert a (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊢[L] ⊥;
    · use T;
      and_intros;
      · exact hT.trans (Finset.subset_insert _ _);
      · intro h₂;
        apply hY;
        have h₃ : (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊢[L] ∼a := Context.deduct h₁;
        have h₄ : (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊢[L] ∼∼a := by
          apply Context.deduct;
          apply Context.weakening _ h₂;
          intro φ;
          have : a ∉ T := fun h ↦ ha (hT h);
          simp only [Set.mem_union, Set.mem_image, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe,
            Finset.mem_insert, Set.mem_insert_iff];
          grind;
        cl_prover [h₃, h₄];
    · use insert a T;
      and_intros;
      · exact Finset.insert_subset_insert _ hT;
      · intro h₂;
        apply h₁;
        apply Context.weakening _ h₂;
        intro φ;
        simp only [Set.mem_union, Set.mem_image, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe,
          Finset.coe_insert, Set.mem_insert_iff];
        grind;

/-- Every consistent set is consistent with some maximal consistent subset of `Φ`. -/
lemma exists_consistent_union (h : X *⊬[L] ⊥) :
    ∃ Γ : MaximalConsistentSet L Φ, (X ∪ Γ.literals) *⊬[L] ⊥ := by
  obtain ⟨T, hT, hY⟩ := exists_consistent_aux h Φ;
  have hc : (↑T ∪ (∼·) '' ↑(Φ \ T)) *⊬[L] ⊥ := by
    intro h₁;
    apply hY <| Context.weakening _ h₁;
    intro φ;
    simp only [Set.mem_union, Set.mem_image];
    tauto;
  use ⟨T, hT, hc⟩;
  simpa [literals, Set.union_assoc] using hY;

end

/-! ### Successors -/

/-- - [dJV90, Definition 3.2] -/
structure Successor (Γ Δ : MaximalConsistentSet L Φ) : Prop where
  mem_of_box_mem : ∀ {A}, □A ∈ Γ → A ∈ Δ
  box_mem_of_box_mem : ∀ {A}, □A ∈ Γ → □A ∈ Δ
  exists_box : ∃ A, □A ∈ Δ ∧ □A ∉ Γ

/-- The formulas `A` with `□A ∈ Γ`. -/
noncomputable def prebox (Γ : MaximalConsistentSet L Φ) : Finset (Formula α) :=
  Γ.set.preimage (□·) fun _ _ _ _ h ↦ box_inj.mp h

variable {Γ Δ Θ : MaximalConsistentSet L Φ}

@[simp] lemma mem_prebox : A ∈ Γ.prebox ↔ □A ∈ Γ := Finset.mem_preimage

namespace Successor

lemma trans (h₁ : Successor Γ Δ) (h₂ : Successor Δ Θ) : Successor Γ Θ := by
  obtain ⟨A, hA, hA'⟩ := h₁.exists_box;
  exact ⟨fun h ↦ h₂.mem_of_box_mem (h₁.box_mem_of_box_mem h),
    fun h ↦ h₂.box_mem_of_box_mem (h₁.box_mem_of_box_mem h), A, h₂.box_mem_of_box_mem hA, hA'⟩

lemma irrefl : ¬Successor Γ Γ := fun h ↦
  have ⟨_, hA, hA'⟩ := h.exists_box;
  hA' hA

lemma prebox_ssubset (h : Successor Γ Δ) : Γ.prebox ⊂ Δ.prebox := by
  obtain ⟨A, hA, hA'⟩ := h.exists_box;
  have h₁ : Γ.prebox ⊆ Δ.prebox := by
    intro B hB;
    simpa using h.box_mem_of_box_mem (mem_prebox.mp hB);
  exact (Finset.ssubset_iff_of_subset h₁).mpr ⟨A, by simpa, by simpa⟩;

lemma not_mem_of_box_neg_mem [Entailment.Cl L] (h : Successor Γ Δ) (hA : □(∼A) ∈ Γ) : A ∉ Δ :=
  not_mem_of_neg_mem <| h.mem_of_box_mem hA

end Successor

variable [Entailment.Cl L]

/-- If `□A ∈ Φ` is not in `Γ`, then `Γ` has a successor consistent with `∼A`.

- [dJV90, Lemma 3.3]
- [KO21, Lemma 4.6]
-/
lemma exists_successor_of_box_not_mem [L.ExtendsGL] [Adequate Φ] (h₁ : □A ∈ Φ) (h₂ : □A ∉ Γ) :
    ∃ Δ, Successor Γ Δ ∧ ({∼A} ∪ Δ.literals) *⊬[L] ⊥ := by
  let X : FormulaSet α := insert (∼A) <| insert (□A) <| {B | □B ∈ Γ} ∪ (□·) '' {B | □B ∈ Γ};
  have hX : X *⊬[L] ⊥ := by
    intro h;
    apply h₂ <| (mem_iff_provable h₁).mpr _;
    have h₃ : ({B | □B ∈ Γ} ∪ (□·) '' {B | □B ∈ Γ}) *⊢[L] □A 🡒 A := by
      have := Context.deduct <| Context.deduct h;
      cl_prover [this];
    have h₄ : Γ.literals *⊢[L] □(□A 🡒 A) := by
      apply Context.weakening _ (box_of_provable h₃);
      rintro _ ⟨B, hB, rfl⟩;
      exact mem_literals hB;
    exact Context.of ExtendsGL.axiomL ⨀ h₄;
  obtain ⟨Δ, hΔ⟩ := exists_consistent_union (Φ := Φ) hX;
  have hm {B} (hB : B ∈ Φ) (h : B ∈ X) : B ∈ Δ := mem_of_provable hΔ hB <| Context.by_axm h;
  use Δ;
  and_intros;
  · exact ⟨fun h ↦ hm (Adequate.box (mem_of_mem h)) (by simp [X, h]),
      fun h ↦ hm (mem_of_mem h) (by simp [X, h]), A, hm h₁ (by simp [X]), h₂⟩;
  · intro h;
    apply hΔ <| Context.weakening _ h;
    intro B;
    simp only [Set.mem_union, Set.mem_singleton_iff];
    rintro (rfl | hB);
    · exact .inl <| Set.mem_insert _ _;
    · exact .inr hB;

/-- `Δ` is a `C`-critical successor of `Γ`.

- [dJV90, Definition 3.5]
-/
structure CriticalSuccessor (C : Formula α) (Γ Δ : MaximalConsistentSet L Φ) : Prop
    extends Successor Γ Δ where
  not_mem : ∀ {A}, A ▷ C ∈ Γ → A ∉ Δ
  box_neg_mem : ∀ {A}, A ▷ C ∈ Γ → □(∼A) ∈ Δ

/-- - [KO21, Lemma 4.4] -/
lemma Successor.criticalSuccessor_bot [Adequate Φ] (hL : ∀ {A}, L ⊢ A ▷ ⊥ 🡒 □(∼A))
    (h : Successor Γ Δ) : CriticalSuccessor ⊥ Γ Δ := by
  have hb {A} (hA : A ▷ ⊥ ∈ Γ) : □(∼A) ∈ Γ :=
    (mem_iff_provable <| Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hA)).mpr <|
      Context.of hL ⨀ Context.by_axm (mem_literals hA);
  exact ⟨h, fun hA ↦ h.not_mem_of_box_neg_mem (hb hA), fun hA ↦ h.box_mem_of_box_mem (hb hA)⟩

/-- - [KO21, Lemma 4.5] -/
lemma CriticalSuccessor.trans_successor (h₁ : CriticalSuccessor C Γ Δ) (h₂ : Successor Δ Θ) :
    CriticalSuccessor C Γ Θ :=
  ⟨h₁.toSuccessor.trans h₂, fun hA ↦ not_mem_of_neg_mem <| h₂.mem_of_box_mem (h₁.box_neg_mem hA),
    fun hA ↦ h₂.box_mem_of_box_mem (h₁.box_neg_mem hA)⟩

lemma exists_box_not_mem [L.ExtendsGL] [Adequate Φ] (h₁ : □A ∈ Φ) (h₂ : □A ∉ Γ) :
    ∃ Δ, Successor Γ Δ ∧ A ∉ Δ := by
  obtain ⟨Δ, hΔ, hc⟩ := exists_successor_of_box_not_mem h₁ h₂;
  use Δ;
  exact ⟨hΔ, not_mem_of_provable_neg hc (Context.by_axm rfl)⟩

lemma exists_neg_consistent (h : L ⊬ A) :
    ∃ Γ : MaximalConsistentSet L Φ, ({∼A} ∪ Γ.literals) *⊬[L] ⊥ := by
  apply exists_consistent_union;
  intro h₁;
  apply h;
  have h₂ : L ⊢ ∼A 🡒 ⊥ := Context.emptyPrf <| Context.deduct <| by simpa using h₁;
  cl_prover [h₂];

/-! ### Existence of critical successors -/

/-- The disjunction of the formulas `A` in `Φ` with `A ▷ F ∈ Γ`. -/
noncomputable def rhdDisj (Γ : MaximalConsistentSet L Φ) (F : Formula α) : Formula α :=
  (Φ.filter (· ▷ F ∈ Γ)).disj

/-- The formulas `B` and `□B` with `□B ∈ Γ`, together with `C`, `□∼C`, `∼H` and `□∼H`, where `H` is
`Γ.rhdDisj F`. -/
noncomputable def criticalSet (Γ : MaximalConsistentSet L Φ) (F C : Formula α) :
    FormulaSet α :=
  insert (∼Γ.rhdDisj F) <| insert (□(∼Γ.rhdDisj F)) <| insert C <| insert (□(∼C)) <|
    {A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ}

section

open Logic.ofAxioms

variable {𝔸 : FormulaSet α} {Γ Δ : MaximalConsistentSet (ofAxioms 𝔸) Φ}


lemma provable_rhd_of_inconsistent (h : Γ.criticalSet F C *⊢[ofAxioms 𝔸] ⊥) :
    Γ.literals *⊢[ofAxioms 𝔸] C ▷ F := by
  have h₁ : ({A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ}) *⊢[ofAxioms 𝔸]
      C ⋏ □(∼C) 🡒 Γ.rhdDisj F ⋎ ∼□(∼Γ.rhdDisj F) := by
    have := Context.deduct <| Context.deduct <| Context.deduct <| Context.deduct h;
    cl_prover [this];
  have h₂ : Γ.literals *⊢[ofAxioms 𝔸] □(C ⋏ □(∼C) 🡒 Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) := by
    apply Context.weakening _ (box_of_provable h₁);
    rintro _ ⟨A, hA, rfl⟩;
    exact mem_literals hA;
  have h₃ : Γ.literals *⊢[ofAxioms 𝔸] Γ.rhdDisj F ▷ F := by
    apply fdisj_rhd;
    intro G hG;
    exact Context.by_axm <| mem_literals (Finset.mem_filter.mp hG).2;
  have h₄ : Γ.literals *⊢[ofAxioms 𝔸] C ▷ (C ⋏ □(∼C)) := Context.of rhd_and_box_neg;
  have h₅ : Γ.literals *⊢[ofAxioms 𝔸] (Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) ▷ Γ.rhdDisj F :=
    Context.of or_dia_rhd;
  have h₆ := Context.of (𝓢 := ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ1 (A := C ⋏ □(∼C)) (B := Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F);
  have h₇ := Context.of (𝓢 := ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ2 (A := C ⋏ □(∼C)) (B := Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) (C := Γ.rhdDisj F);
  have h₈ := Context.of (𝓢 := ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ2 (A := C) (B := C ⋏ □(∼C)) (C := Γ.rhdDisj F);
  have h₉ := Context.of (𝓢 := ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ2 (A := C) (B := Γ.rhdDisj F) (C := F);
  cl_prover [h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉];

variable [Adequate Φ]

lemma exists_criticalSuccessor_of_consistent_union (hC : IsRhdOperand Φ C)
    (h : (Γ.criticalSet F C ∪ X) *⊬[ofAxioms 𝔸] ⊥) (hs : □(∼C) ∉ Γ) :
    ∃ Δ, CriticalSuccessor F Γ Δ ∧ C ∈ Δ ∧ (X ∪ Δ.literals) *⊬[ofAxioms 𝔸] ⊥ := by
  obtain ⟨Δ, hΔ⟩ := exists_consistent_union (Φ := Φ) h;
  have hm {A} (hA : A ∈ Φ) (h : A ∈ Γ.criticalSet F C) : A ∈ Δ :=
    mem_of_provable hΔ hA <| Context.by_axm <| .inl h;
  have hb {A} (hA : □A ∈ Γ) : A ∈ Δ ∧ □A ∈ Δ :=
    ⟨hm (Adequate.box (mem_of_mem hA)) <| by simp [criticalSet, hA],
      hm (mem_of_mem hA) <| by simp [criticalSet, hA]⟩;
  have hG {G} (hG : G ▷ F ∈ Γ) : G ∉ Δ ∧ □(∼G) ∈ Δ := by
    have h₁ : G ∈ Φ.filter (· ▷ F ∈ Γ) :=
      Finset.mem_filter.mpr ⟨Adequate.rhd_left (mem_of_mem hG), hG⟩;
    have h₂ : ofAxioms 𝔸 ⊢ G 🡒 Γ.rhdDisj F := right_Fdisj_intro _ h₁;
    have h₃ : ofAxioms 𝔸 ⊢ □(∼Γ.rhdDisj F) 🡒 □(∼G) := box_mono <| by cl_prover [h₂];
    have h₄ : (Γ.criticalSet F C ∪ X) *⊢[ofAxioms 𝔸] ∼Γ.rhdDisj F :=
      Context.by_axm <| .inl <| by simp [criticalSet];
    have h₅ : (Γ.criticalSet F C ∪ X) *⊢[ofAxioms 𝔸] □(∼Γ.rhdDisj F) :=
      Context.by_axm <| .inl <| by simp [criticalSet];
    constructor;
    · apply not_mem_of_provable_neg hΔ;
      have h₆ := Context.of (𝓢 := ofAxioms 𝔸) (Γ := Γ.criticalSet F C ∪ X) h₂;
      cl_prover [h₄, h₆];
    · exact mem_of_provable hΔ (Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hG)) <|
        Context.of h₃ ⨀ h₅;
  use Δ;
  and_intros;
  · exact ⟨⟨fun h ↦ (hb h).1, fun h ↦ (hb h).2,
      ∼C, hm (Adequate.box_neg_mem hC) (by simp [criticalSet]), hs⟩,
      fun h ↦ (hG h).1, fun h ↦ (hG h).2⟩;
  · exact hm hC.mem (by simp [criticalSet]);
  · intro h₁;
    apply hΔ <| Context.weakening _ h₁;
    intro A;
    simp only [Set.mem_union];
    tauto;

lemma exists_criticalSuccessor_of_consistent (hC : IsRhdOperand Φ C)
    (h : Γ.criticalSet F C *⊬[ofAxioms 𝔸] ⊥) (hs : □(∼C) ∉ Γ) :
    ∃ Δ, CriticalSuccessor F Γ Δ ∧ C ∈ Δ := by
  obtain ⟨Δ, hΔ, hCΔ, -⟩ :=
    exists_criticalSuccessor_of_consistent_union (X := ∅) hC (by simpa using h) hs;
  use Δ;

/-- - [dJV90, Lemma 3.6] -/
lemma exists_criticalSuccessor_of_rhd_not_mem (h₁ : B ▷ C ∈ Φ) (h₂ : B ▷ C ∉ Γ) :
    ∃ Δ, CriticalSuccessor C Γ Δ ∧ B ∈ Δ := by
  apply exists_criticalSuccessor_of_consistent (.of_rhd_left h₁);
  · intro h;
    exact h₂ <| (mem_iff_provable h₁).mpr <| provable_rhd_of_inconsistent h;
  · intro h;
    apply h₂ <| (mem_iff_provable h₁).mpr _;
    have h₃ : ofAxioms 𝔸 ⊢ □(∼B) 🡒 B ▷ C := C_trans (box_mono <| by cl_prover) axiomJ1;
    exact Context.of h₃ ⨀ Context.by_axm (mem_literals h);

/-- - [dJV90, Lemma 3.7] -/
lemma CriticalSuccessor.exists_criticalSuccessor (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ)
    (hΔ : CriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, CriticalSuccessor F Γ Θ ∧ E ∈ Θ := by
  have hD' : IsRhdOperand Φ D := .of_rhd_left (mem_of_mem hDE);
  apply exists_criticalSuccessor_of_consistent (.of_rhd_right (mem_of_mem hDE));
  · intro h;
    apply hΔ.not_mem _ hD;
    apply (mem_iff_provable <| Adequate.rhd_mem hD' hF).mpr;
    have h₁ := provable_rhd_of_inconsistent h;
    have h₂ := Context.of (𝓢 := ofAxioms 𝔸) (Γ := Γ.literals) <|
      axiomJ2 (A := D) (B := E) (C := F);
    have h₃ : Γ.literals *⊢[ofAxioms 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
    cl_prover [h₁, h₂, h₃];
  · intro h;
    apply hΔ.toSuccessor.not_mem_of_box_neg_mem _ hD;
    apply (mem_iff_provable <| Adequate.box_neg_mem hD').mpr;
    exact Context.of box_neg_of_rhd ⨀ Context.by_axm (mem_literals hDE) ⨀
      Context.by_axm (mem_literals h);

end

end MaximalConsistentSet

/-! ### Adequate sets -/

/-- `Φ` is adequate and contains `□(B 🡒 ⋁S)` for every antecedent or consequent `B` of a
`▷`-formula in `Φ` and every finite set `S` of such formulas and of their `◇`-formulas.

- [KO21, Definition 4.1]
-/
class ILMinusAdequate (Φ : Finset (Formula α)) : Prop extends Adequate Φ where
  box_imp_disj_mem {B : Formula α} {S : Finset (Formula α)} : IsRhdOperand Φ B →
    (∀ A ∈ S, IsRhdOperand Φ A ∨ ∃ G, IsRhdOperand Φ G ∧ A = ◇G) → □(B 🡒 S.disj) ∈ Φ

/-- A finite set satisfying `ILMinusAdequate` and containing `S`. -/
noncomputable def ilMinusAdequateClosure (S : Finset (Formula α)) : Finset (Formula α) :=
  let T := insert ⊥ (S.biUnion subformulas);
  (T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪
    (T ×ˢ (T ∪ T.image (◇·)).powerset).image (fun p ↦ □(p.1 🡒 p.2.disj))).biUnion subformulas

namespace ilMinusAdequateClosure

variable {S T : Finset (Formula α)} {A B C : Formula α}

/-- Every `▷`-subformula of `A` has both of its components in `T`. -/
private def RhdClosed (T : Finset (Formula α)) (A : Formula α) : Prop :=
  ∀ B C, B ▷ C ∈ A.subformulas → B ∈ T ∧ C ∈ T

private lemma rhdClosed_bot : RhdClosed T ⊥ := by
  intro B C h;
  simp [subformulas] at h;

private lemma rhdClosed_imp (hA : RhdClosed T A) (hB : RhdClosed T B) : RhdClosed T (A 🡒 B) := by
  intro B' C' h;
  simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
  rcases h with h | h | h;
  · simp at h;
  · exact hA B' C' h;
  · exact hB B' C' h;

private lemma rhdClosed_box (hA : RhdClosed T A) : RhdClosed T (□A) := by
  intro B C h;
  simp only [subformulas, Finset.mem_insert] at h;
  rcases h with h | h;
  · simp at h;
  · exact hA B C h;

private lemma rhdClosed_disj : (l : List (Formula α)) → (∀ A ∈ l, RhdClosed T A) →
    RhdClosed T l.disj₂
  | [], _ => rhdClosed_bot
  | [A], h => h A (by simp)
  | A :: B :: l, h =>
    rhdClosed_imp (rhdClosed_imp (h A (by simp)) rhdClosed_bot) <|
      rhdClosed_disj (B :: l) fun C hC ↦ h C (by simp_all)

private lemma base_closed (hA : A ∈ insert ⊥ (S.biUnion subformulas)) (hB : B ∈ A.subformulas) :
    B ∈ insert ⊥ (S.biUnion subformulas) := by
  simp only [Finset.mem_insert, Finset.mem_biUnion] at hA ⊢;
  rcases hA with rfl | ⟨C, hC, hA⟩;
  · simp_all [subformulas];
  · exact .inr ⟨C, hC, subformulas_subset_of_mem hA hB⟩

private lemma rhdClosed_of_base (hA : A ∈ insert ⊥ (S.biUnion subformulas)) :
    RhdClosed (insert ⊥ (S.biUnion subformulas)) A := by
  intro B C h;
  have h₁ := base_closed hA h;
  constructor;
  · exact base_closed h₁ (by simp [subformulas]);
  · exact base_closed h₁ (by simp [subformulas]);

private lemma rhdClosed_of_mem_gen {g : Formula α}
    (hg : g ∈ (let T := insert ⊥ (S.biUnion subformulas);
      T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪
        (T ×ˢ (T ∪ T.image (◇·)).powerset).image (fun p ↦ □(p.1 🡒 p.2.disj)))) :
    RhdClosed (insert ⊥ (S.biUnion subformulas)) g := by
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_powerset,
    Prod.exists] at hg;
  rcases hg with ((hg | ⟨B, C, ⟨hB, hC⟩, rfl⟩) | ⟨B, hB, rfl⟩) | ⟨B, U, ⟨hB, hU⟩, rfl⟩;
  · exact rhdClosed_of_base hg;
  · intro B' C' h;
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with h | h | h;
    · obtain ⟨rfl, rfl⟩ := rhd_inj.mp h;
      exact ⟨hB, hC⟩;
    · exact rhdClosed_of_base hB B' C' h;
    · exact rhdClosed_of_base hC B' C' h;
  · exact rhdClosed_box <| rhdClosed_imp (rhdClosed_of_base hB) rhdClosed_bot;
  · apply rhdClosed_box <| rhdClosed_imp (rhdClosed_of_base hB) <| rhdClosed_disj _ _;
    intro A hA;
    rcases Finset.mem_union.mp (hU (Finset.mem_toList.mp hA)) with hA | hA;
    · exact rhdClosed_of_base hA;
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hA;
      exact rhdClosed_imp (rhdClosed_box <| rhdClosed_imp (rhdClosed_of_base hG) rhdClosed_bot)
        rhdClosed_bot;

private lemma mem_sub (hA : A ∈ ilMinusAdequateClosure S) (hB : B ∈ A.subformulas) :
    B ∈ ilMinusAdequateClosure S := by
  obtain ⟨g, hg, hA⟩ := Finset.mem_biUnion.mp hA;
  exact Finset.mem_biUnion.mpr ⟨g, hg, subformulas_subset_of_mem hA hB⟩

private lemma mem_of_gen {g : Formula α}
    (hg : g ∈ (let T := insert ⊥ (S.biUnion subformulas);
      T ∪ (T ×ˢ T).image (fun p ↦ p.1 ▷ p.2) ∪ T.image (fun A ↦ □(∼A)) ∪
        (T ×ˢ (T ∪ T.image (◇·)).powerset).image (fun p ↦ □(p.1 🡒 p.2.disj)))) :
    g ∈ ilMinusAdequateClosure S :=
  Finset.mem_biUnion.mpr ⟨g, hg, mem_subformulas_self⟩

private lemma isRhdOperand (h : IsRhdOperand (ilMinusAdequateClosure S) A) :
    A ∈ insert ⊥ (S.biUnion subformulas) := by
  obtain ⟨B, h | h⟩ := h <;> obtain ⟨g, hg, h⟩ := Finset.mem_biUnion.mp h;
  · exact (rhdClosed_of_mem_gen hg _ _ h).1;
  · exact (rhdClosed_of_mem_gen hg _ _ h).2;

lemma subset : S ⊆ ilMinusAdequateClosure S := by
  intro A hA;
  apply mem_of_gen;
  simp only [Finset.mem_union];
  exact .inl <| .inl <| .inl <| Finset.mem_insert_of_mem <|
    Finset.mem_biUnion.mpr ⟨A, hA, mem_subformulas_self⟩

instance : ILMinusAdequate (ilMinusAdequateClosure S) where
  imp_left h := mem_sub h (by simp [subformulas])
  imp_right h := mem_sub h (by simp [subformulas])
  box h := mem_sub h (by simp [subformulas])
  rhd_left h := mem_sub h (by simp [subformulas])
  rhd_right h := mem_sub h (by simp [subformulas])
  bot_rhd_bot := mem_of_gen <| by simp
  rhd_mem {A B} hA hB := mem_of_gen <| Finset.mem_union_left _ <| Finset.mem_union_left _ <|
    Finset.mem_union_right _ <|
      Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨isRhdOperand hA, isRhdOperand hB⟩, rfl⟩
  box_neg_mem hA := mem_of_gen <| Finset.mem_union_left _ <| Finset.mem_union_right _ <|
    Finset.mem_image_of_mem _ (isRhdOperand hA)
  box_imp_disj_mem {B U} hB hU := by
    apply mem_of_gen;
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_powerset,
      Prod.exists];
    have hU' : U ⊆ insert ⊥ (S.biUnion subformulas) ∪
        (insert ⊥ (S.biUnion subformulas)).image (◇·) := by
      intro A hA;
      rcases hU A hA with hA | ⟨G, hG, rfl⟩;
      · exact Finset.mem_union_left _ (isRhdOperand hA);
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (isRhdOperand hG));
    exact .inr ⟨B, U, ⟨isRhdOperand hB, hU'⟩, rfl⟩;

end ilMinusAdequateClosure

/-! ### Successors -/

namespace MaximalConsistentSet

open Logic Logic.ofAxiomsMinus

/-- `Δ` is a successor of `Γ` that contains no `A` with `A ▷ C ∈ Γ`.

- [KO21, Definition 4.3]
-/
structure WeakCriticalSuccessor {L : Logic α} {Φ : Finset (Formula α)} (C : Formula α)
    (Γ Δ : MaximalConsistentSet L Φ) : Prop extends Successor Γ Δ where
  not_mem : ∀ {A}, A ▷ C ∈ Γ → A ∉ Δ

lemma CriticalSuccessor.weakCriticalSuccessor {L : Logic α} {Φ : Finset (Formula α)}
    {C : Formula α} {Γ Δ : MaximalConsistentSet L Φ} (h : CriticalSuccessor C Γ Δ) :
    WeakCriticalSuccessor C Γ Δ :=
  ⟨h.toSuccessor, h.not_mem⟩

variable {𝔸 : FormulaSet α} {Φ : Finset (Formula α)} [ILMinusAdequate Φ]
  {Γ Δ : MaximalConsistentSet (ofAxiomsMinus 𝔸) Φ} {B D E F : Formula α} {S : Finset (Formula α)}

private lemma exists_successor_of_box_imp_disj_not_mem (hB : IsRhdOperand Φ B)
    (hS : ∀ A ∈ S, IsRhdOperand Φ A ∨ ∃ G, IsRhdOperand Φ G ∧ A = ◇G)
    (h : □(B 🡒 S.disj) ∉ Γ) :
    ∃ Δ, Successor Γ Δ ∧ B ∈ Δ ∧
      (∀ {P}, P ∈ Φ → ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 P → P ∈ Δ) ∧
      ∀ {P}, ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 ∼P → P ∉ Δ := by
  obtain ⟨Δ, hΔ, hc⟩ := exists_successor_of_box_not_mem (ILMinusAdequate.box_imp_disj_mem hB hS) h;
  have hH : ({∼(B 🡒 S.disj)} : FormulaSet α) *⊢[ofAxiomsMinus 𝔸] ∼(B 🡒 S.disj) :=
    Context.by_axm rfl;
  have h₁ {P} (hP : ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 P) :
      ({∼(B 🡒 S.disj)} : FormulaSet α) *⊢[ofAxiomsMinus 𝔸] P := by
    have := Context.of (Γ := {∼(B 🡒 S.disj)}) hP;
    cl_prover [hH, this];
  use Δ;
  and_intros;
  · exact hΔ;
  · exact mem_of_provable hc hB.mem <| by cl_prover [hH];
  · intro P hP h;
    exact mem_of_provable hc hP (h₁ h);
  · intro P h;
    exact not_mem_of_provable_neg hc (h₁ h);

omit [ILMinusAdequate Φ] in
private lemma provable_rhd_of_box_imp_disj_mem
    (hS : ∀ A ∈ S, Γ.literals *⊢[ofAxiomsMinus 𝔸] A ▷ F) (h : □(B 🡒 S.disj) ∈ Γ) :
    Γ.literals *⊢[ofAxiomsMinus 𝔸] B ▷ F :=
  Context.of rhd_anti_left_of_box ⨀ Context.by_axm (mem_literals h) ⨀ fdisj_rhd hS

private lemma mem_rhdSet {G : Formula α} : G ∈ Φ.filter (· ▷ F ∈ Γ) ↔ G ▷ F ∈ Γ :=
  ⟨fun h ↦ (Finset.mem_filter.mp h).2,
    fun h ↦ Finset.mem_filter.mpr ⟨Adequate.rhd_left (mem_of_mem h), h⟩⟩

private lemma provable_neg_of_mem {G : Formula α} (h : G ∈ S) :
    ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 ∼G := by
  have := right_Fdisj_intro (𝓢 := ofAxiomsMinus 𝔸) S h;
  cl_prover [this];

private lemma provable_box_neg_of_mem {G : Formula α} (h : ◇G ∈ S) :
    ofAxiomsMinus 𝔸 ⊢ ∼S.disj 🡒 □(∼G) := by
  have : ofAxiomsMinus 𝔸 ⊢ ∼□(∼G) 🡒 S.disj := right_Fdisj_intro S h;
  cl_prover [this];

private lemma rhd_of_mem_diaSet [(ofAxiomsMinus 𝔸).HasAxiomJ2]
    [(ofAxiomsMinus 𝔸).HasAxiomJ5] {A : Formula α}
    (h : A ∈ insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))) :
    Γ.literals *⊢[ofAxiomsMinus 𝔸] A ▷ F := by
  have hJ5 {G : Formula α} : Γ.literals *⊢[ofAxiomsMinus 𝔸] ◇G ▷ G :=
    Context.of (HasAxiomJ5.J5 _);
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
  rcases h with rfl | h | ⟨G, hG, rfl⟩;
  · exact hJ5;
  · exact Context.by_axm <| mem_literals <| mem_rhdSet.mp h;
  · have h₁ := Context.of (Γ := Γ.literals) <| HasAxiomJ2.J2 (L := ofAxiomsMinus 𝔸) (◇G) G F;
    have h₂ : Γ.literals *⊢[ofAxiomsMinus 𝔸] G ▷ F :=
      Context.by_axm <| mem_literals <| mem_rhdSet.mp hG;
    have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] ◇G ▷ G := hJ5;
    cl_prover [h₁, h₂, h₃];

private lemma diaSet_spec (hF : IsRhdOperand Φ F) {A : Formula α}
    (h : A ∈ insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))) :
    IsRhdOperand Φ A ∨ ∃ G, IsRhdOperand Φ G ∧ A = ◇G := by
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h;
  rcases h with rfl | h | ⟨G, hG, rfl⟩;
  · exact .inr ⟨F, hF, rfl⟩;
  · exact .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp h;
  · exact .inr ⟨G, .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hG, rfl⟩;

private lemma criticalSuccessor_of_diaSet (hΔ : Successor Γ Δ)
    (hn : ∀ {P}, ofAxiomsMinus 𝔸 ⊢
      ∼(insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))).disj 🡒 ∼P →
        P ∉ Δ)
    (hp : ∀ {P}, P ∈ Φ → ofAxiomsMinus 𝔸 ⊢
      ∼(insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·))).disj 🡒 P →
        P ∈ Δ) :
    CriticalSuccessor F Γ Δ := by
  constructor;
  · exact hΔ;
  · intro A hA;
    exact hn <| provable_neg_of_mem <| by simp [mem_rhdSet.mpr hA];
  · intro A hA;
    apply hp (Adequate.box_neg_mem <| .of_rhd_left <| mem_of_mem hA);
    apply provable_box_neg_of_mem;
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image];
    exact .inr <| .inr ⟨_, mem_rhdSet.mpr hA, rfl⟩;

/-- - [KO21, Lemma 4.6] -/
lemma exists_weakCriticalSuccessor_of_rhd_not_mem (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ Γ) :
    ∃ Δ, WeakCriticalSuccessor E Γ Δ ∧ D ∈ Δ := by
  obtain ⟨Δ, hΔ, hD, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := Φ.filter (· ▷ E ∈ Γ)) (.of_rhd_left h₁)
    (fun A hA ↦ .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      exact h₂ <| (mem_iff_provable h₁).mpr <| provable_rhd_of_box_imp_disj_mem
        (fun G hG ↦ Context.by_axm <| mem_literals <| mem_rhdSet.mp hG) h;
  use Δ;
  and_intros;
  · exact ⟨hΔ, fun hG ↦ hn <| provable_neg_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hD;

/-- - [KO21, Lemma 4.6.a] -/
lemma exists_weakCriticalSuccessor_box_neg_of_rhd_not_mem
    [(ofAxiomsMinus 𝔸).HasAxiomJ5] (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ Γ) :
    ∃ Δ, WeakCriticalSuccessor E Γ Δ ∧ D ∈ Δ ∧ □(∼E) ∈ Δ := by
  have hE : IsRhdOperand Φ E := .of_rhd_right h₁;
  obtain ⟨Δ, hΔ, hD, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := insert (◇E) (Φ.filter (· ▷ E ∈ Γ))) (.of_rhd_left h₁) (by
      intro A hA;
      rcases Finset.mem_insert.mp hA with rfl | hA;
      · exact .inr ⟨E, hE, rfl⟩;
      · exact .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      apply h₂ <| (mem_iff_provable h₁).mpr <| provable_rhd_of_box_imp_disj_mem _ h;
      intro A hA;
      rcases Finset.mem_insert.mp hA with rfl | hA;
      · exact Context.of (HasAxiomJ5.J5 _);
      · exact Context.by_axm <| mem_literals <| mem_rhdSet.mp hA;
  use Δ;
  and_intros;
  · exact ⟨hΔ, fun hG ↦ hn <| provable_neg_of_mem <|
      Finset.mem_insert_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hD;
  · exact hp (Adequate.box_neg_mem hE) <| provable_box_neg_of_mem <| Finset.mem_insert_self _ _;

/-- - [KO21, Lemma 4.6.b] -/
lemma exists_criticalSuccessor_box_neg_of_rhd_not_mem [(ofAxiomsMinus 𝔸).HasAxiomJ2]
    [(ofAxiomsMinus 𝔸).HasAxiomJ5] (h₁ : D ▷ E ∈ Φ) (h₂ : D ▷ E ∉ Γ) :
    ∃ Δ, CriticalSuccessor E Γ Δ ∧ D ∈ Δ ∧ □(∼E) ∈ Δ := by
  have hE : IsRhdOperand Φ E := .of_rhd_right h₁;
  obtain ⟨Δ, hΔ, hD, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (.of_rhd_left h₁) (fun _ ↦ diaSet_spec hE) <| by
      intro h;
      exact h₂ <| (mem_iff_provable h₁).mpr <|
        provable_rhd_of_box_imp_disj_mem (fun _ h ↦ rhd_of_mem_diaSet (Γ := Γ) h) h;
  use Δ;
  and_intros;
  · exact criticalSuccessor_of_diaSet hΔ hn hp;
  · exact hD;
  · exact hp (Adequate.box_neg_mem hE) <| provable_box_neg_of_mem <| Finset.mem_insert_self _ _;

namespace WeakCriticalSuccessor

private lemma rhd_not_mem (hF : IsRhdOperand Φ F) (hΔ : WeakCriticalSuccessor F Γ Δ)
    (hDE : D ▷ E ∈ Γ) (hD : D ∈ Δ) : Γ.literals *⊬[ofAxiomsMinus 𝔸] D ▷ F := fun h ↦
  hΔ.not_mem ((mem_iff_provable <| Adequate.rhd_mem (.of_rhd_left (mem_of_mem hDE)) hF).mpr h) hD

/-- - [KO21, Lemma 4.7] -/
lemma exists_mem_not_mem (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ)
    (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ : MaximalConsistentSet (ofAxiomsMinus 𝔸) Φ, E ∈ Θ ∧ F ∉ Θ := by
  have hX : (insert E {∼F} : FormulaSet α) *⊬[ofAxiomsMinus 𝔸] ⊥ := by
    intro h;
    apply rhd_not_mem hF hΔ hDE hD;
    have h₁ : ofAxiomsMinus 𝔸 ⊢ ∼F 🡒 E 🡒 ⊥ :=
      Context.emptyPrf <| Context.deduct <| by simpa using Context.deduct h;
    have h₂ : ofAxiomsMinus 𝔸 ⊢ D ▷ E 🡒 D ▷ F := rhd_mono_right <| by cl_prover [h₁];
    exact Context.of h₂ ⨀ Context.by_axm (mem_literals hDE);
  obtain ⟨Θ, hΘ⟩ := exists_consistent_union (Φ := Φ) hX;
  use Θ;
  and_intros;
  · exact mem_of_provable hΘ (Adequate.rhd_right (mem_of_mem hDE)) (Context.by_axm (by simp));
  · exact not_mem_of_provable_neg hΘ (Context.by_axm (by simp));

/-- - [KO21, Lemma 4.7.a] -/
lemma exists_successor_mem_not_mem [(ofAxiomsMinus 𝔸).HasAxiomJ4Plus]
    (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ) (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, Successor Γ Θ ∧ E ∈ Θ ∧ F ∉ Θ := by
  have hd : ({F} : Finset (Formula α)).disj = F := by simp [Finset.disj];
  obtain ⟨Θ, hΘ, hE, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem (S := {F})
    (.of_rhd_right (mem_of_mem hDE)) (by simpa using .inl hF) <| by
      intro h;
      apply rhd_not_mem hF hΔ hDE hD;
      rw [hd] at h;
      have h₁ : ofAxiomsMinus 𝔸 ⊢ □(E 🡒 F) 🡒 D ▷ E 🡒 D ▷ F :=
        HasAxiomJ4Plus.J4Plus _ _ _;
      exact Context.of h₁ ⨀ Context.by_axm (mem_literals h) ⨀ Context.by_axm (mem_literals hDE);
  use Θ;
  and_intros;
  · exact hΘ;
  · exact hE;
  · exact hn <| by rw [hd]; exact C_id;

omit [ILMinusAdequate Φ] in
/-- If `□(E 🡒 ⋁(insert F X))` is in `Γ`, where `Γ` proves `G ▷ F` for every `G ∈ X`, then `Γ` proves
`D ▷ F` for every `D ▷ E ∈ Γ`. -/
private lemma provable_rhd_of_box_imp_insert_disj_mem [(ofAxiomsMinus 𝔸).HasAxiomJ2Plus]
    (hS : ∀ A ∈ S, Γ.literals *⊢[ofAxiomsMinus 𝔸] A ▷ F) (hDE : D ▷ E ∈ Γ)
    (h : □(E 🡒 (insert F S).disj) ∈ Γ) : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ F := by
  have h₁ : ofAxiomsMinus 𝔸 ⊢ (insert F S).disj 🡒 F ⋎ S.disj := CinsertFDisjAFDisj;
  have h₂ : Γ.literals *⊢[ofAxiomsMinus 𝔸] □(E ⋏ ∼F 🡒 S.disj) :=
    Context.of (box_mono <| by cl_prover [h₁]) ⨀ Context.by_axm (mem_literals h);
  have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] (E ⋏ ∼F) ▷ F :=
    Context.of rhd_anti_left_of_box ⨀ h₂ ⨀ fdisj_rhd hS;
  have h₄ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ ((E ⋏ ∼F) ⋎ F) :=
    Context.of (rhd_mono_right <| by cl_prover) ⨀ Context.by_axm (mem_literals hDE);
  have h₅ := Context.of (Γ := Γ.literals) <|
    HasAxiomJ2Plus.J2Plus (L := ofAxiomsMinus 𝔸) D (E ⋏ ∼F) F;
  cl_prover [h₃, h₄, h₅];

/-- - [KO21, Lemma 4.7.b] -/
lemma exists_weakCriticalSuccessor_mem_not_mem [(ofAxiomsMinus 𝔸).HasAxiomJ2Plus]
    (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ) (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, WeakCriticalSuccessor F Γ Θ ∧ E ∈ Θ ∧ F ∉ Θ := by
  obtain ⟨Θ, hΘ, hE, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := insert F (Φ.filter (· ▷ F ∈ Γ))) (.of_rhd_right (mem_of_mem hDE)) (by
      intro A hA;
      rcases Finset.mem_insert.mp hA with rfl | hA;
      · exact .inl hF;
      · exact .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      exact rhd_not_mem hF hΔ hDE hD <| provable_rhd_of_box_imp_insert_disj_mem
        (fun G hG ↦ Context.by_axm <| mem_literals <| mem_rhdSet.mp hG) hDE h;
  use Θ;
  and_intros;
  · exact ⟨hΘ, fun hG ↦ hn <| provable_neg_of_mem <|
      Finset.mem_insert_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hE;
  · exact hn <| provable_neg_of_mem <| Finset.mem_insert_self _ _;

/-- - [KO21, Lemma 4.7.c] -/
lemma exists_criticalSuccessor_box_neg_mem_not_mem [(ofAxiomsMinus 𝔸).HasAxiomJ2Plus]
    [(ofAxiomsMinus 𝔸).HasAxiomJ5] (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ)
    (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, CriticalSuccessor F Γ Θ ∧ E ∈ Θ ∧ F ∉ Θ ∧ □(∼F) ∈ Θ := by
  let T := insert (◇F) (Φ.filter (· ▷ F ∈ Γ) ∪ (Φ.filter (· ▷ F ∈ Γ)).image (◇·));
  obtain ⟨Θ, hΘ, hE, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem (S := insert F T)
    (.of_rhd_right (mem_of_mem hDE)) (by
      intro A hA;
      rcases Finset.mem_insert.mp hA with rfl | hA;
      · exact .inl hF;
      · exact diaSet_spec hF hA) <| by
      intro h;
      exact rhd_not_mem hF hΔ hDE hD <| provable_rhd_of_box_imp_insert_disj_mem
        (fun _ h ↦ rhd_of_mem_diaSet (Γ := Γ) h) hDE h;
  have hT : ofAxiomsMinus 𝔸 ⊢ ∼(insert F T).disj 🡒 ∼T.disj := by
    have : ofAxiomsMinus 𝔸 ⊢ T.disj 🡒 (insert F T).disj :=
      CFDisjFDisj_of_subset (Finset.subset_insert _ _);
    cl_prover [this];
  use Θ;
  and_intros;
  · exact criticalSuccessor_of_diaSet hΘ (fun h ↦ hn <| C_trans hT h)
      (fun hP h ↦ hp hP <| C_trans hT h);
  · exact hE;
  · exact hn <| provable_neg_of_mem <| Finset.mem_insert_self _ _;
  · exact hp (Adequate.box_neg_mem hF) <| provable_box_neg_of_mem <|
      Finset.mem_insert_of_mem <| Finset.mem_insert_self _ _;

/-- - [KO21, Lemma 4.9] -/
lemma exists_weakCriticalSuccessor_of_rhd_mem [(ofAxiomsMinus 𝔸).HasAxiomJ2]
    (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ) (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, WeakCriticalSuccessor F Γ Θ ∧ E ∈ Θ := by
  obtain ⟨Θ, hΘ, hE, -, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (S := Φ.filter (· ▷ F ∈ Γ)) (.of_rhd_right (mem_of_mem hDE))
    (fun A hA ↦ .inl <| .of_rhd_left <| mem_of_mem <| mem_rhdSet.mp hA) <| by
      intro h;
      apply rhd_not_mem hF hΔ hDE hD;
      have h₁ := provable_rhd_of_box_imp_disj_mem
        (fun G hG ↦ Context.by_axm <| mem_literals <| mem_rhdSet.mp hG) h;
      have h₂ := Context.of (Γ := Γ.literals) <| HasAxiomJ2.J2 (L := ofAxiomsMinus 𝔸) D E F;
      have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
      cl_prover [h₁, h₂, h₃];
  use Θ;
  and_intros;
  · exact ⟨hΘ, fun hG ↦ hn <| provable_neg_of_mem <| mem_rhdSet.mpr hG⟩;
  · exact hE;

/-- - [KO21, Lemma 4.9.a] -/
lemma exists_criticalSuccessor_box_neg_of_rhd_mem [(ofAxiomsMinus 𝔸).HasAxiomJ2]
    [(ofAxiomsMinus 𝔸).HasAxiomJ5] (hF : IsRhdOperand Φ F) (hDE : D ▷ E ∈ Γ)
    (hΔ : WeakCriticalSuccessor F Γ Δ) (hD : D ∈ Δ) :
    ∃ Θ, CriticalSuccessor F Γ Θ ∧ E ∈ Θ ∧ □(∼F) ∈ Θ := by
  obtain ⟨Θ, hΘ, hE, hp, hn⟩ := exists_successor_of_box_imp_disj_not_mem
    (.of_rhd_right (mem_of_mem hDE)) (fun _ ↦ diaSet_spec hF) <| by
      intro h;
      apply rhd_not_mem hF hΔ hDE hD;
      have h₁ := provable_rhd_of_box_imp_disj_mem (fun _ h ↦ rhd_of_mem_diaSet (Γ := Γ) h) h;
      have h₂ := Context.of (Γ := Γ.literals) <| HasAxiomJ2.J2 (L := ofAxiomsMinus 𝔸) D E F;
      have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
      cl_prover [h₁, h₂, h₃];
  use Θ;
  and_intros;
  · exact criticalSuccessor_of_diaSet hΘ hn hp;
  · exact hE;
  · exact hp (Adequate.box_neg_mem hF) <| provable_box_neg_of_mem <| Finset.mem_insert_self _ _;

end WeakCriticalSuccessor

omit [ILMinusAdequate Φ] in
/-- - [KO21, Lemma 4.8] -/
lemma Successor.exists_successor_of_rhd_mem [Adequate Φ] [(ofAxiomsMinus 𝔸).HasAxiomJ4]
    (hDE : D ▷ E ∈ Γ) (hΔ : Successor Γ Δ) (hD : D ∈ Δ) : ∃ Θ, Successor Γ Θ ∧ E ∈ Θ := by
  have hE : IsRhdOperand Φ E := .of_rhd_right (mem_of_mem hDE);
  obtain ⟨Θ, hΘ, hc⟩ := exists_successor_of_box_not_mem (Adequate.box_neg_mem hE) <| by
    intro h;
    apply hΔ.not_mem_of_box_neg_mem _ hD;
    apply (mem_iff_provable <| Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hDE)).mpr;
    have h₁ := Context.of (Γ := Γ.literals) <| HasAxiomJ4.J4 (L := ofAxiomsMinus 𝔸) D E;
    have h₂ : Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
    have h₃ : Γ.literals *⊢[ofAxiomsMinus 𝔸] □(∼E) := Context.by_axm (mem_literals h);
    change Γ.literals *⊢[ofAxiomsMinus 𝔸] D ▷ E 🡒 ∼□(∼D) 🡒 ∼□(∼E) at h₁;
    cl_prover [h₁, h₂, h₃];
  use Θ;
  and_intros;
  · exact hΘ;
  · have : ({∼∼E} : FormulaSet α) *⊢[ofAxiomsMinus 𝔸] ∼∼E := Context.by_axm rfl;
    exact mem_of_provable hc hE.mem <| by cl_prover [this];

end MaximalConsistentSet

end FFL.InterpretabilityLogic

end
