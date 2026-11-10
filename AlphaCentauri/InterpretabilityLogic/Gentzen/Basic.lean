module

public import AlphaCentauri.InterpretabilityLogic.Formula
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import AlphaCentauri.InterpretabilityLogic.Logic.Basic

/-!
# A sequent calculus for $\mathbf{IL}$

Subformulas, sequents of finite sets of formulas, and the extension of a sequent on which a
predicate fails to a saturated one. A cut-free sequent calculus for $\mathbf{IL}$ in the language
with a primitive `□`, whose modal rules are those of $\mathbf{GIL}$, with `A ▷ ⊥` written `□∼A`, the
boxes on the left treated as in the calculus of $\mathbf{GL}$, and a rule for `□` on the right.

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

end FFL.InterpretabilityLogic

end
