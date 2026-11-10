module

public import AlphaCentauri.InterpretabilityLogic.Formula
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max

/-!
# Sequents of interpretability logic

Subformulas, sequents of finite sets of formulas, and the extension of a sequent on which a
predicate fails to a saturated one.
-/

@[expose] public section

namespace FFL.InterpretabilityLogic

abbrev FormulaFinset (α : Type*) := Finset (Formula α)

namespace Formula

variable {α : Type*} [DecidableEq α] {A B : Formula α}

def subfmls : Formula α → FormulaFinset α
  | #a    => {#a}
  | ⊥     => {⊥}
  | A 🡒 B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
  | □A    => insert (□A) A.subfmls
  | A ▷ B => insert (A ▷ B) (A.subfmls ∪ B.subfmls)

@[simp, grind .] lemma mem_subfmls_self : A ∈ A.subfmls := by cases A <;> simp [subfmls];

@[simp, grind .] lemma mem_subfmls_imp_left : A ∈ (A 🡒 B).subfmls := by simp [subfmls];

@[simp, grind .] lemma mem_subfmls_imp_right : B ∈ (A 🡒 B).subfmls := by simp [subfmls];

@[simp, grind .] lemma mem_subfmls_box : A ∈ (□A).subfmls := by simp [subfmls];

@[simp, grind .] lemma mem_subfmls_rhd_left : A ∈ (A ▷ B).subfmls := by simp [subfmls];

@[simp, grind .] lemma mem_subfmls_rhd_right : B ∈ (A ▷ B).subfmls := by simp [subfmls];

lemma mem_subfmls_trans {C : Formula α} (hB : B ∈ A.subfmls) (hC : C ∈ B.subfmls) :
    C ∈ A.subfmls := by
  induction A with
  | atom a => simp_all [subfmls];
  | falsum => simp_all [subfmls];
  | imp A₁ A₂ ih₁ ih₂ =>
    simp only [subfmls, Finset.mem_insert, Finset.mem_union] at hB ⊢;
    rcases hB with rfl | hB | hB;
    · simpa [subfmls] using hC;
    · exact Or.inr (Or.inl (ih₁ hB));
    · exact Or.inr (Or.inr (ih₂ hB));
  | box A ih =>
    simp only [subfmls, Finset.mem_insert] at hB ⊢;
    rcases hB with rfl | hB;
    · simpa [subfmls] using hC;
    · exact Or.inr (ih hB);
  | rhd A₁ A₂ ih₁ ih₂ =>
    simp only [subfmls, Finset.mem_insert, Finset.mem_union] at hB ⊢;
    rcases hB with rfl | hB | hB;
    · simpa [subfmls] using hC;
    · exact Or.inr (Or.inl (ih₁ hB));
    · exact Or.inr (Or.inr (ih₂ hB));

end Formula

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

def subfmls (Γ : FormulaFinset α) : FormulaFinset α := Γ.biUnion Formula.subfmls

@[grind .] lemma subset_subfmls : Γ ⊆ Γ.subfmls :=
  fun A hA ↦ Finset.mem_biUnion.mpr ⟨A, hA, Formula.mem_subfmls_self⟩

@[grind →]
lemma mem_subfmls_subfmls {C : Formula α} (hB : B ∈ Γ.subfmls) (hC : C ∈ B.subfmls) :
    C ∈ Γ.subfmls := by
  obtain ⟨A, hA, hBA⟩ := Finset.mem_biUnion.mp hB;
  exact Finset.mem_biUnion.mpr ⟨A, hA, Formula.mem_subfmls_trans hBA hC⟩

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

def subfmls (S : Sequent α) : FormulaFinset α := S.ant.subfmls ∪ S.suc.subfmls

/-- `D` holds of every sequent sharing a formula between its two sides and is closed under the
implication rules; typically `D` is derivability in a sequent calculus. -/
structure IsImpClosed (D : Sequent α → Prop) : Prop where
  union {S : Sequent α} {A : Formula α} : A ∈ S.ant → A ∈ S.suc → D S
  impL {Γ Δ : FormulaFinset α} {A B : Formula α} :
    D (Γ ⟹ insert A Δ) → D (insert B Γ ⟹ Δ) → D (insert (A 🡒 B) Γ ⟹ Δ)
  impR {Γ Δ : FormulaFinset α} {A B : Formula α} :
    D (insert A Γ ⟹ insert B Δ) → D (Γ ⟹ insert (A 🡒 B) Δ)

/-- Every sequent within `P` on which `D` fails extends to a saturated one within `P` on which `D`
fails, provided `P` contains the components of its implications. -/
theorem exists_saturated {D : Sequent α → Prop} (hD : IsImpClosed D) {P : FormulaFinset α}
    (hP : ∀ {A B}, A 🡒 B ∈ P → A ∈ P ∧ B ∈ P) {S₀ : Sequent α} (h₀ : ¬D S₀)
    (hant : S₀.ant ⊆ P) (hsuc : S₀.suc ⊆ P) :
    ∃ S, S₀ ⊆ S ∧ ¬D S ∧ S.Saturated ∧ S.ant ⊆ P ∧ S.suc ⊆ P := by
  classical
  let C := (P.powerset ×ˢ P.powerset).filter
    fun p ↦ S₀.ant ⊆ p.1 ∧ S₀.suc ⊆ p.2 ∧ ¬D (p.1 ⟹ p.2);
  have hC : (S₀.ant, S₀.suc) ∈ C := by simp [C, hant, hsuc, h₀];
  obtain ⟨⟨Γ, Δ⟩, hp, hmax⟩ := C.exists_max_image (fun p ↦ p.1.card + p.2.card) ⟨_, hC⟩;
  simp only [C, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hp;
  obtain ⟨⟨hΓ, hΔ⟩, h₁, h₂, hD'⟩ := hp;
  have grow : ∀ {Γ' Δ'}, Γ ⊆ Γ' → Δ ⊆ Δ' → Γ' ⊆ P → Δ' ⊆ P → ¬D (Γ' ⟹ Δ') →
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
      by_cases hl : D (Γ ⟹ insert A Δ);
      · by_cases hr : D (insert B Γ ⟹ Δ);
        · exact absurd (by simpa [Finset.insert_eq_of_mem hAB] using hD.impL hl hr) hD';
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
      have hn : ¬D (insert A Γ ⟹ insert B Δ) := fun h ↦
        hD' (by simpa [Finset.insert_eq_of_mem hAB] using hD.impR h);
      obtain ⟨e₁, e₂⟩ := grow (Finset.subset_insert A Γ) (Finset.subset_insert B Δ)
        (Finset.insert_subset hA hΓ) (Finset.insert_subset hB hΔ) hn;
      rw [← e₁, ← e₂];
      exact ⟨Finset.mem_insert_self A Γ, Finset.mem_insert_self B Δ⟩;
  · exact hΓ;
  · exact hΔ;

end Sequent

end FFL.InterpretabilityLogic

end
