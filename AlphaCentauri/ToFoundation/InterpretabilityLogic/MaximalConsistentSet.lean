module

public import AlphaCentauri.ToFoundation.InterpretabilityLogic.Logic

/-!
# Maximal consistent subsets of adequate sets

Finite adequate sets of formulas, the maximal consistent subsets of such a set relative to an
extension of $\mathbf{IL}$, and their (critical) successors.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

open Entailment Formula

variable {α : Type*}

/-! ### Theorems of extensions of $\mathbf{IL}$ -/

namespace Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {A B : Formula α}

lemma provable_box (h : ofAxioms 𝔸 ⊢ A) : ofAxioms 𝔸 ⊢ □A := nec h

lemma box_and : ofAxioms 𝔸 ⊢ □A ⋏ □B 🡒 □(A ⋏ B) := by
  have h₁ : ofAxioms 𝔸 ⊢ □A 🡒 □(B 🡒 A ⋏ B) := box_mono and₃;
  have h₂ : ofAxioms 𝔸 ⊢ □(B 🡒 A ⋏ B) 🡒 □B 🡒 □(A ⋏ B) := axiomK;
  cl_prover [h₁, h₂];

lemma axiom4 : ofAxioms 𝔸 ⊢ □A 🡒 □□A := by
  have h₁ : ofAxioms 𝔸 ⊢ □(□A ⋏ A) 🡒 □A := box_mono and₂;
  have h₂ : ofAxioms 𝔸 ⊢ □A 🡒 □(□(□A ⋏ A) 🡒 □A ⋏ A) := box_mono <| by cl_prover [h₁];
  have h₃ : ofAxioms 𝔸 ⊢ □(□(□A ⋏ A) 🡒 □A ⋏ A) 🡒 □(□A ⋏ A) := axiomL;
  have h₄ : ofAxioms 𝔸 ⊢ □(□A ⋏ A) 🡒 □□A := box_mono and₁;
  cl_prover [h₂, h₃, h₄];

lemma rhd_refl : ofAxioms 𝔸 ⊢ A ▷ A := axiomJ1 ⨀ provable_box (by cl_prover)

lemma box_neg_of_rhd : ofAxioms 𝔸 ⊢ A ▷ B 🡒 □(∼B) 🡒 □(∼A) := by
  have h : ofAxioms 𝔸 ⊢ A ▷ B 🡒 ∼□(∼A) 🡒 ∼□(∼B) := axiomJ4;
  cl_prover [h];

lemma box_neg_of_rhd_bot : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼A) := by
  have h₁ : ofAxioms 𝔸 ⊢ □(∼⊥) := provable_box verum;
  have h₂ : ofAxioms 𝔸 ⊢ A ▷ ⊥ 🡒 □(∼⊥) 🡒 □(∼A) := box_neg_of_rhd;
  cl_prover [h₁, h₂];

lemma or_dia_rhd : ofAxioms 𝔸 ⊢ (A ⋎ ◇A) ▷ A := by
  have h₁ : ofAxioms 𝔸 ⊢ A ▷ A := rhd_refl;
  have h₂ : ofAxioms 𝔸 ⊢ ◇A ▷ A := axiomJ5;
  have h₃ : ofAxioms 𝔸 ⊢ A ▷ A ⋏ ◇A ▷ A 🡒 (A ⋎ ◇A) ▷ A := axiomJ3;
  cl_prover [h₁, h₂, h₃];

lemma rhd_and_box_neg : ofAxioms 𝔸 ⊢ A ▷ (A ⋏ □(∼A)) := by
  have h₁ : ofAxioms 𝔸 ⊢ □(□(∼A) 🡒 ∼A) 🡒 □(∼A) := axiomL;
  have h₂ : ofAxioms 𝔸 ⊢ □(∼(A ⋏ □(∼A))) 🡒 □(□(∼A) 🡒 ∼A) := box_mono <| by cl_prover;
  have h₃ : ofAxioms 𝔸 ⊢ A ▷ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) :=
    axiomJ1 ⨀ provable_box
      (show ofAxioms 𝔸 ⊢ A 🡒 (A ⋏ □(∼A)) ⋎ ∼□(∼(A ⋏ □(∼A))) by cl_prover [h₁, h₂]);
  have h₄ : ofAxioms 𝔸 ⊢ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) := or_dia_rhd;
  have h₅ : ofAxioms 𝔸 ⊢
      A ▷ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ⋏ ((A ⋏ □(∼A)) ⋎ ◇(A ⋏ □(∼A))) ▷ (A ⋏ □(∼A)) 🡒
        A ▷ (A ⋏ □(∼A)) :=
    axiomJ2;
  cl_prover [h₃, h₄, h₅];

variable {X : Set (Formula α)}

lemma box_conj_of_forall {X : Set (Formula α)} :
    (Δ : List (Formula α)) → (∀ B ∈ Δ, X *⊢[ofAxioms 𝔸] □B) → X *⊢[ofAxioms 𝔸] □Δ.conj
  | [], _ => Context.of <| provable_box verum
  | B :: Δ, h =>
    Context.of box_and ⨀
      K_intro (h B (by simp)) (box_conj_of_forall Δ fun C hC ↦ h C (by simp [hC]))

/-- If `A` follows from `T` together with the formulas `□B` for `B ∈ T`, then `□A` follows from the
latter. -/
lemma box_of_provable {T : Set (Formula α)} (h : (T ∪ (□·) '' T) *⊢[ofAxioms 𝔸] A) :
    ((□·) '' T) *⊢[ofAxioms 𝔸] □A := by
  obtain ⟨Δ, hΔ, hb⟩ := Context.provable_iff.mp h;
  have h₁ : ofAxioms 𝔸 ⊢ □Δ.conj 🡒 □A :=
    box_mono <| C_trans (K_right EConj₂Conj) (FiniteContext.provable_iff.mp hb);
  apply Context.of h₁ ⨀ box_conj_of_forall Δ _;
  intro B hB;
  rcases hΔ B hB with hB | ⟨C, hC, rfl⟩;
  · exact Context.by_axm ⟨B, hB, rfl⟩;
  · exact Context.of axiom4 ⨀ Context.by_axm ⟨C, hC, rfl⟩;

variable [DecidableEq α] {F : Formula α}

lemma fdisj_rhd {𝒢 : Finset (Formula α)} (h : ∀ G ∈ 𝒢, X *⊢[ofAxioms 𝔸] G ▷ F) :
    X *⊢[ofAxioms 𝔸] 𝒢.disj ▷ F := by
  induction 𝒢 using Finset.induction_on with
  | empty => simpa using Context.of (axiomJ1 ⨀ provable_box efq);
  | insert G 𝒢 _ ih =>
    have h₁ : X *⊢[ofAxioms 𝔸] (G ⋎ 𝒢.disj) ▷ F :=
      Context.of axiomJ3 ⨀ K_intro (h G (by simp)) (ih fun H hH ↦ h H (by simp [hH]));
    exact Context.of (rhd_anti_left CinsertFDisjAFDisj) ⨀ h₁;

end Logic.ofAxioms

/-! ### Subformulas and adequate sets -/

variable [DecidableEq α]

namespace Formula

def subformulas : Formula α → Finset (Formula α)
  | #a    => {#a}
  | ⊥     => {⊥}
  | A 🡒 B => insert (A 🡒 B) (A.subformulas ∪ B.subformulas)
  | □A    => insert (□A) A.subformulas
  | A ▷ B => insert (A ▷ B) (A.subformulas ∪ B.subformulas)

variable {A B : Formula α}

@[simp] lemma mem_subformulas_self : A ∈ A.subformulas := by
  cases A <;> simp [subformulas];

lemma subformulas_subset_of_mem (h : B ∈ A.subformulas) : B.subformulas ⊆ A.subformulas := by
  induction A with
  | atom a => simp_all [subformulas];
  | falsum => simp_all [subformulas];
  | imp A₁ A₂ ih₁ ih₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    · rfl;
    · exact (ih₁ h).trans <| fun x hx ↦ by simp [subformulas, hx];
    · exact (ih₂ h).trans <| fun x hx ↦ by simp [subformulas, hx];
  | box A ih =>
    simp only [subformulas, Finset.mem_insert] at h;
    rcases h with rfl | h;
    · rfl;
    · exact (ih h).trans <| fun x hx ↦ by simp [subformulas, hx];
  | rhd A₁ A₂ ih₁ ih₂ =>
    simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h;
    rcases h with rfl | h | h;
    · rfl;
    · exact (ih₁ h).trans <| fun x hx ↦ by simp [subformulas, hx];
    · exact (ih₂ h).trans <| fun x hx ↦ by simp [subformulas, hx];

end Formula

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
`Γ`, is consistent in `ofAxioms 𝔸`. -/
structure MaximalConsistentSet (𝔸 : Set (Formula α)) (Φ : Finset (Formula α)) where
  set : Finset (Formula α)
  subset : set ⊆ Φ
  consistent : (↑set ∪ (∼·) '' ↑(Φ \ set)) *⊬[Logic.ofAxioms 𝔸] ⊥

namespace MaximalConsistentSet

open Logic.ofAxioms

variable {𝔸 : Set (Formula α)} {Φ : Finset (Formula α)} {X : Set (Formula α)}
  {A B C D E F : Formula α}

section

variable {Γ : MaximalConsistentSet 𝔸 Φ}

instance : Membership (Formula α) (MaximalConsistentSet 𝔸 Φ) := ⟨fun Γ A ↦ A ∈ Γ.set⟩

lemma mem_def : A ∈ Γ ↔ A ∈ Γ.set := Iff.rfl

instance : DecidablePred (· ∈ Γ) := fun A ↦ inferInstanceAs (Decidable (A ∈ Γ.set))

lemma ext {Γ Δ : MaximalConsistentSet 𝔸 Φ} (h : Γ.set = Δ.set) : Γ = Δ := by
  cases Γ; cases Δ; simp_all;

instance : Finite (MaximalConsistentSet 𝔸 Φ) :=
  Finite.of_injective (β := Φ.powerset) (fun Γ ↦ ⟨Γ.set, Finset.mem_powerset.mpr Γ.subset⟩)
    fun _ _ h ↦ ext <| by simpa using h

lemma mem_of_mem (h : A ∈ Γ) : A ∈ Φ := Γ.subset h

/-- The formulas of `Γ` together with the negations of the formulas in `Φ` outside `Γ`. -/
def literals (Γ : MaximalConsistentSet 𝔸 Φ) : Set (Formula α) := ↑Γ.set ∪ (∼·) '' ↑(Φ \ Γ.set)

lemma mem_literals (h : A ∈ Γ) : A ∈ Γ.literals := .inl h

lemma neg_mem_literals (hA : A ∈ Φ) (h : A ∉ Γ) : ∼A ∈ Γ.literals :=
  .inr ⟨A, by simpa using ⟨hA, h⟩, rfl⟩

lemma consistent_literals : Γ.literals *⊬[Logic.ofAxioms 𝔸] ⊥ := Γ.consistent

lemma mem_of_provable (hX : (X ∪ Γ.literals) *⊬[Logic.ofAxioms 𝔸] ⊥) (hA : A ∈ Φ)
    (h : X *⊢[Logic.ofAxioms 𝔸] A) : A ∈ Γ := by
  by_contra hn;
  apply hX;
  have h₁ : (X ∪ Γ.literals) *⊢[Logic.ofAxioms 𝔸] A := Context.weakening Set.subset_union_left h;
  have h₂ : (X ∪ Γ.literals) *⊢[Logic.ofAxioms 𝔸] ∼A :=
    Context.by_axm <| .inr <| neg_mem_literals hA hn;
  cl_prover [h₁, h₂];

lemma not_mem_of_provable_neg (hX : (X ∪ Γ.literals) *⊬[Logic.ofAxioms 𝔸] ⊥)
    (h : X *⊢[Logic.ofAxioms 𝔸] ∼A) : A ∉ Γ := by
  intro hm;
  apply hX;
  have h₁ : (X ∪ Γ.literals) *⊢[Logic.ofAxioms 𝔸] ∼A := Context.weakening Set.subset_union_left h;
  have h₂ : (X ∪ Γ.literals) *⊢[Logic.ofAxioms 𝔸] A := Context.by_axm <| .inr <| mem_literals hm;
  cl_prover [h₁, h₂];

lemma mem_iff_provable (hA : A ∈ Φ) : A ∈ Γ ↔ Γ.literals *⊢[Logic.ofAxioms 𝔸] A :=
  ⟨fun h ↦ Context.by_axm <| mem_literals h,
    mem_of_provable (by simpa using consistent_literals) hA⟩

lemma provable_neg_of_not_mem (hA : A ∈ Φ) (h : A ∉ Γ) : Γ.literals *⊢[Logic.ofAxioms 𝔸] ∼A :=
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

private lemma exists_consistent_aux (h : X *⊬[Logic.ofAxioms 𝔸] ⊥) (S : Finset (Formula α)) :
    ∃ T ⊆ S, (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊬[Logic.ofAxioms 𝔸] ⊥ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simpa using h⟩;
  | @insert a S ha ih =>
    obtain ⟨T, hT, hY⟩ := ih;
    by_cases h₁ : insert a (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊢[Logic.ofAxioms 𝔸] ⊥;
    · use T;
      and_intros;
      · exact hT.trans (Finset.subset_insert _ _);
      · intro h₂;
        apply hY;
        have h₃ : (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊢[Logic.ofAxioms 𝔸] ∼a := Context.deduct h₁;
        have h₄ : (X ∪ ↑T ∪ (∼·) '' ↑(S \ T)) *⊢[Logic.ofAxioms 𝔸] ∼∼a := by
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
lemma exists_consistent_union (h : X *⊬[Logic.ofAxioms 𝔸] ⊥) :
    ∃ Γ : MaximalConsistentSet 𝔸 Φ, (X ∪ Γ.literals) *⊬[Logic.ofAxioms 𝔸] ⊥ := by
  obtain ⟨T, hT, hY⟩ := exists_consistent_aux h Φ;
  have hc : (↑T ∪ (∼·) '' ↑(Φ \ T)) *⊬[Logic.ofAxioms 𝔸] ⊥ := by
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
structure Successor (Γ Δ : MaximalConsistentSet 𝔸 Φ) : Prop where
  mem_of_box_mem : ∀ {A}, □A ∈ Γ → A ∈ Δ
  box_mem_of_box_mem : ∀ {A}, □A ∈ Γ → □A ∈ Δ
  exists_box : ∃ A, □A ∈ Δ ∧ □A ∉ Γ

/-- The formulas `A` with `□A ∈ Γ`. -/
noncomputable def prebox (Γ : MaximalConsistentSet 𝔸 Φ) : Finset (Formula α) :=
  Γ.set.preimage (□·) fun _ _ _ _ h ↦ box_inj.mp h

variable {Γ Δ Θ : MaximalConsistentSet 𝔸 Φ}

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

lemma not_mem_of_box_neg_mem (h : Successor Γ Δ) (hA : □(∼A) ∈ Γ) : A ∉ Δ :=
  not_mem_of_neg_mem <| h.mem_of_box_mem hA

end Successor

/-- - [dJV90, Lemma 3.3] -/
lemma exists_successor_of_box_not_mem [Adequate Φ] (h₁ : □A ∈ Φ) (h₂ : □A ∉ Γ) :
    ∃ Δ, Successor Γ Δ ∧ A ∉ Δ := by
  let X : Set (Formula α) := insert (∼A) <| insert (□A) <| {B | □B ∈ Γ} ∪ (□·) '' {B | □B ∈ Γ};
  have hX : X *⊬[Logic.ofAxioms 𝔸] ⊥ := by
    intro h;
    apply h₂ <| (mem_iff_provable h₁).mpr _;
    have h₃ : ({B | □B ∈ Γ} ∪ (□·) '' {B | □B ∈ Γ}) *⊢[Logic.ofAxioms 𝔸] □A 🡒 A := by
      have := Context.deduct <| Context.deduct h;
      cl_prover [this];
    have h₄ : Γ.literals *⊢[Logic.ofAxioms 𝔸] □(□A 🡒 A) := by
      apply Context.weakening _ (box_of_provable h₃);
      rintro _ ⟨B, hB, rfl⟩;
      exact mem_literals hB;
    exact Context.of axiomL ⨀ h₄;
  obtain ⟨Δ, hΔ⟩ := exists_consistent_union (Φ := Φ) hX;
  have hm {B} (hB : B ∈ Φ) (h : B ∈ X) : B ∈ Δ := mem_of_provable hΔ hB <| Context.by_axm h;
  use Δ;
  and_intros;
  · exact ⟨fun h ↦ hm (Adequate.box (mem_of_mem h)) (by simp [X, h]),
      fun h ↦ hm (mem_of_mem h) (by simp [X, h]), A, hm h₁ (by simp [X]), h₂⟩;
  · exact not_mem_of_provable_neg hΔ (Context.by_axm <| by simp [X]);

/-- `Δ` is a `C`-critical successor of `Γ`.

- [dJV90, Definition 3.5]
-/
structure CriticalSuccessor (C : Formula α) (Γ Δ : MaximalConsistentSet 𝔸 Φ) : Prop
    extends Successor Γ Δ where
  not_mem : ∀ {A}, A ▷ C ∈ Γ → A ∉ Δ
  box_neg_mem : ∀ {A}, A ▷ C ∈ Γ → □(∼A) ∈ Δ

/-- - [KO21, Lemma 4.4] -/
lemma Successor.criticalSuccessor_bot [Adequate Φ] (h : Successor Γ Δ) :
    CriticalSuccessor ⊥ Γ Δ := by
  have hb {A} (hA : A ▷ ⊥ ∈ Γ) : □(∼A) ∈ Γ :=
    (mem_iff_provable <| Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hA)).mpr <|
      Context.of box_neg_of_rhd_bot ⨀ Context.by_axm (mem_literals hA);
  exact ⟨h, fun hA ↦ h.not_mem_of_box_neg_mem (hb hA), fun hA ↦ h.box_mem_of_box_mem (hb hA)⟩

/-- - [KO21, Lemma 4.5] -/
lemma CriticalSuccessor.trans_successor (h₁ : CriticalSuccessor C Γ Δ) (h₂ : Successor Δ Θ) :
    CriticalSuccessor C Γ Θ :=
  ⟨h₁.toSuccessor.trans h₂, fun hA ↦ not_mem_of_neg_mem <| h₂.mem_of_box_mem (h₁.box_neg_mem hA),
    fun hA ↦ h₂.box_mem_of_box_mem (h₁.box_neg_mem hA)⟩

/-! ### Existence of critical successors -/

/-- The disjunction of the formulas `A` in `Φ` with `A ▷ F ∈ Γ`. -/
noncomputable def rhdDisj (Γ : MaximalConsistentSet 𝔸 Φ) (F : Formula α) : Formula α :=
  (Φ.filter (· ▷ F ∈ Γ)).disj

/-- The formulas `B` and `□B` with `□B ∈ Γ`, together with `C`, `□∼C`, `∼H` and `□∼H`, where `H` is
`Γ.rhdDisj F`. -/
noncomputable def criticalSet (Γ : MaximalConsistentSet 𝔸 Φ) (F C : Formula α) :
    Set (Formula α) :=
  insert (∼Γ.rhdDisj F) <| insert (□(∼Γ.rhdDisj F)) <| insert C <| insert (□(∼C)) <|
    {A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ}

lemma provable_rhd_of_inconsistent (h : Γ.criticalSet F C *⊢[Logic.ofAxioms 𝔸] ⊥) :
    Γ.literals *⊢[Logic.ofAxioms 𝔸] C ▷ F := by
  have h₁ : ({A | □A ∈ Γ} ∪ (□·) '' {A | □A ∈ Γ}) *⊢[Logic.ofAxioms 𝔸]
      C ⋏ □(∼C) 🡒 Γ.rhdDisj F ⋎ ∼□(∼Γ.rhdDisj F) := by
    have := Context.deduct <| Context.deduct <| Context.deduct <| Context.deduct h;
    cl_prover [this];
  have h₂ : Γ.literals *⊢[Logic.ofAxioms 𝔸] □(C ⋏ □(∼C) 🡒 Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) := by
    apply Context.weakening _ (box_of_provable h₁);
    rintro _ ⟨A, hA, rfl⟩;
    exact mem_literals hA;
  have h₃ : Γ.literals *⊢[Logic.ofAxioms 𝔸] Γ.rhdDisj F ▷ F := by
    apply fdisj_rhd;
    intro G hG;
    exact Context.by_axm <| mem_literals (Finset.mem_filter.mp hG).2;
  have h₄ : Γ.literals *⊢[Logic.ofAxioms 𝔸] C ▷ (C ⋏ □(∼C)) := Context.of rhd_and_box_neg;
  have h₅ : Γ.literals *⊢[Logic.ofAxioms 𝔸] (Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) ▷ Γ.rhdDisj F :=
    Context.of or_dia_rhd;
  have h₆ := Context.of (𝓢 := Logic.ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ1 (A := C ⋏ □(∼C)) (B := Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F);
  have h₇ := Context.of (𝓢 := Logic.ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ2 (A := C ⋏ □(∼C)) (B := Γ.rhdDisj F ⋎ ◇Γ.rhdDisj F) (C := Γ.rhdDisj F);
  have h₈ := Context.of (𝓢 := Logic.ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ2 (A := C) (B := C ⋏ □(∼C)) (C := Γ.rhdDisj F);
  have h₉ := Context.of (𝓢 := Logic.ofAxioms 𝔸) (Γ := Γ.literals) <|
    axiomJ2 (A := C) (B := Γ.rhdDisj F) (C := F);
  cl_prover [h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉];

variable [Adequate Φ]

lemma exists_criticalSuccessor_of_consistent (hC : IsRhdOperand Φ C)
    (h : Γ.criticalSet F C *⊬[Logic.ofAxioms 𝔸] ⊥) (hs : □(∼C) ∉ Γ) :
    ∃ Δ, CriticalSuccessor F Γ Δ ∧ C ∈ Δ := by
  obtain ⟨Δ, hΔ⟩ := exists_consistent_union (Φ := Φ) h;
  have hm {A} (hA : A ∈ Φ) (h : A ∈ Γ.criticalSet F C) : A ∈ Δ :=
    mem_of_provable hΔ hA <| Context.by_axm h;
  have hb {A} (hA : □A ∈ Γ) : A ∈ Δ ∧ □A ∈ Δ :=
    ⟨hm (Adequate.box (mem_of_mem hA)) <| by simp [criticalSet, hA],
      hm (mem_of_mem hA) <| by simp [criticalSet, hA]⟩;
  have hG {G} (hG : G ▷ F ∈ Γ) : G ∉ Δ ∧ □(∼G) ∈ Δ := by
    have h₁ : G ∈ Φ.filter (· ▷ F ∈ Γ) :=
      Finset.mem_filter.mpr ⟨Adequate.rhd_left (mem_of_mem hG), hG⟩;
    have h₂ : Logic.ofAxioms 𝔸 ⊢ G 🡒 Γ.rhdDisj F := right_Fdisj_intro _ h₁;
    have h₃ : Logic.ofAxioms 𝔸 ⊢ □(∼Γ.rhdDisj F) 🡒 □(∼G) := box_mono <| by cl_prover [h₂];
    have h₄ : Γ.criticalSet F C *⊢[Logic.ofAxioms 𝔸] ∼Γ.rhdDisj F :=
      Context.by_axm <| by simp [criticalSet];
    have h₅ : Γ.criticalSet F C *⊢[Logic.ofAxioms 𝔸] □(∼Γ.rhdDisj F) :=
      Context.by_axm <| by simp [criticalSet];
    constructor;
    · apply not_mem_of_provable_neg hΔ;
      have h₆ := Context.of (𝓢 := Logic.ofAxioms 𝔸) (Γ := Γ.criticalSet F C) h₂;
      cl_prover [h₄, h₆];
    · exact mem_of_provable hΔ (Adequate.box_neg_mem <| .of_rhd_left (mem_of_mem hG)) <|
        Context.of h₃ ⨀ h₅;
  use Δ;
  and_intros;
  · exact ⟨⟨fun h ↦ (hb h).1, fun h ↦ (hb h).2,
      ∼C, hm (Adequate.box_neg_mem hC) (by simp [criticalSet]), hs⟩,
      fun h ↦ (hG h).1, fun h ↦ (hG h).2⟩;
  · exact hm hC.mem (by simp [criticalSet]);

/-- - [dJV90, Lemma 3.6] -/
lemma exists_criticalSuccessor_of_rhd_not_mem (h₁ : B ▷ C ∈ Φ) (h₂ : B ▷ C ∉ Γ) :
    ∃ Δ, CriticalSuccessor C Γ Δ ∧ B ∈ Δ := by
  apply exists_criticalSuccessor_of_consistent (.of_rhd_left h₁);
  · intro h;
    exact h₂ <| (mem_iff_provable h₁).mpr <| provable_rhd_of_inconsistent h;
  · intro h;
    apply h₂ <| (mem_iff_provable h₁).mpr _;
    have h₃ : Logic.ofAxioms 𝔸 ⊢ □(∼B) 🡒 B ▷ C := C_trans (box_mono <| by cl_prover) axiomJ1;
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
    have h₂ := Context.of (𝓢 := Logic.ofAxioms 𝔸) (Γ := Γ.literals) <|
      axiomJ2 (A := D) (B := E) (C := F);
    have h₃ : Γ.literals *⊢[Logic.ofAxioms 𝔸] D ▷ E := Context.by_axm (mem_literals hDE);
    cl_prover [h₁, h₂, h₃];
  · intro h;
    apply hΔ.toSuccessor.not_mem_of_box_neg_mem _ hD;
    apply (mem_iff_provable <| Adequate.box_neg_mem hD').mpr;
    exact Context.of box_neg_of_rhd ⨀ Context.by_axm (mem_literals hDE) ⨀
      Context.by_axm (mem_literals h);

end MaximalConsistentSet

end FFL.InterpretabilityLogic

end
