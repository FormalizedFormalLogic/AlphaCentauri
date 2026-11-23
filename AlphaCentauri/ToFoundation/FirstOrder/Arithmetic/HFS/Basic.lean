module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# Hereditarily finite sets in models of arithmetic

Insertions into a coded set commute and are absorbed. `listUnion v` is the union of the coded sets
listed in the vector `v`. `cardBelow s n` is the number of elements of the coded set `s` below `n`,
and `card s` is the number of elements of `s`.
-/

@[expose] public section

/-! ## Elementary facts about coded sets -/

namespace FFL.FirstOrder
namespace Arithmetic

open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {a n p s v x y Γ : V}

attribute [local grind =] mem_bitInsert_iff mem_bitRemove_iff

lemma insert_comm (x y s : V) : insert x (insert y s) = insert y (insert x s) :=
  mem_ext fun _ ↦ by grind

lemma insert_insert_self (x s : V) : insert x (insert x s) = insert x s :=
  mem_ext fun _ ↦ by grind

lemma insert_pair_absorb (x y s : V) :
    insert x (insert y (insert x (insert y s))) = insert x (insert y s) :=
  mem_ext fun _ ↦ by grind

lemma insert_pair_comm (x y a s : V) :
    insert x (insert y (insert a s)) = insert a (insert x (insert y s)) :=
  mem_ext fun _ ↦ by grind

lemma insert_pair_comm₂ (x y a b s : V) :
    insert x (insert y (insert a (insert b s))) = insert a (insert b (insert x (insert y s))) :=
  mem_ext fun _ ↦ by grind

lemma mem_of_mem_insert_of_ne (h : x ∈ insert y s) (hne : x ≠ y) : x ∈ s :=
  (mem_bitInsert_iff.mp h).resolve_left hne

lemma insert_subset_insert_insert (h : Γ ⊆ insert p s) : insert a Γ ⊆ insert p (insert a s) := by
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · simp
  · rcases mem_bitInsert_iff.mp (h hx) with rfl | hx
    · simp
    · simp [hx]

/-! ## The union of a list of coded sets -/

namespace ListUnion

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. !unionDef y x ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ∅
  adjoin _ x _ ih := x ∪ ih
  nil_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end ListUnion

section

open ListUnion

/-- The union of the coded sets listed in the vector `v`. -/
noncomputable def listUnion (v : V) : V := construction.result ![] v

@[simp]
lemma listUnion_nil : listUnion (0 : V) = ∅ := by simp [listUnion, construction]

@[simp]
lemma listUnion_adjoin (x v : V) : listUnion (x ∷ v) = x ∪ listUnion v := by
  simp [listUnion, construction]

section

def _root_.FFL.FirstOrder.Arithmetic.listUnionDef : 𝚺ᴬ₁.Semisentence 2 := blueprint.resultDef

instance listUnion_defined : 𝚺ᴬ₁-Function₁ (listUnion : V → V) via listUnionDef :=
  construction.result_defined

instance listUnion_definable : 𝚺ᴬ₁-Function₁ (listUnion : V → V) :=
  listUnion_defined.to_definable

instance listUnion_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (listUnion : V → V) :=
  listUnion_definable.of_sigmaOne

end

@[simp]
lemma mem_listUnion_iff : x ∈ listUnion v ↔ ∃ i < len v, x ∈ v.[i] := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin y v ih =>
    rw [listUnion_adjoin, mem_cup_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · exact ⟨i + 1, by simpa using hi, by simpa using h⟩
    · rintro ⟨i, hi, h⟩
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · left; simpa using h
      · right; exact ⟨i, by simpa using hi, by simpa using h⟩

lemma listUnion_eq_empty_iff : listUnion v = ∅ ↔ ∀ i < len v, v.[i] = ∅ := by
  simp only [mem_ext_iff, mem_listUnion_iff, not_mem_empty, iff_false, not_exists, not_and]
  exact ⟨fun h i hi x hx ↦ h x i hi hx, fun h x i hi hx ↦ h i hi x hx⟩

end

/-! ## The number of elements of a coded set -/

namespace CardBelow

def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y s. y = 0”
  succ := .mkSigma “y ih n s. (n ∈ s ∧ y = ih + 1) ∨ (¬n ∈ s ∧ y = ih)”

open Classical in
noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ s n ih := if n ∈ s 0 then ih + 1 else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by by_cases h : v 2 ∈ v 3 <;> simp [blueprint, h]

end CardBelow

open CardBelow

/-- The number of elements of the coded set `s` below `n`. -/
noncomputable def cardBelow (s n : V) : V := construction.result ![s] n

@[simp]
lemma cardBelow_zero (s : V) : cardBelow s 0 = 0 := by
  simp [cardBelow, construction]

open Classical in
lemma cardBelow_succ (s n : V) :
    cardBelow s (n + 1) = if n ∈ s then cardBelow s n + 1 else cardBelow s n := by
  simp [cardBelow, construction]

/-- The number of elements of the coded set `s`. -/
noncomputable def card (s : V) : V := cardBelow s s

section

def _root_.FFL.FirstOrder.Arithmetic.cardBelowDef : 𝚺ᴬ₁.Semisentence 3 :=
  blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance cardBelow_defined : 𝚺ᴬ₁-Function₂ (cardBelow : V → V → V) via cardBelowDef := .mk
  fun v ↦ by simp [construction.result_defined_iff, cardBelowDef]; rfl

instance cardBelow_definable : 𝚺ᴬ₁-Function₂ (cardBelow : V → V → V) :=
  cardBelow_defined.to_definable

instance cardBelow_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (cardBelow : V → V → V) :=
  cardBelow_definable.of_sigmaOne

def _root_.FFL.FirstOrder.Arithmetic.cardDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y s. !cardBelowDef y s s”

instance card_defined : 𝚺ᴬ₁-Function₁ (card : V → V) via cardDef := .mk
  fun v ↦ by
    simp only [cardDef, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    simp [card]

instance card_definable : 𝚺ᴬ₁-Function₁ (card : V → V) := card_defined.to_definable

instance card_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (card : V → V) :=
  card_definable.of_sigmaOne

end

lemma cardBelow_eq_zero_iff : cardBelow s n = 0 ↔ ∀ i < n, i ∉ s := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [cardBelow_succ]
    split_ifs with h
    · exact iff_of_false (by simp) fun H ↦ H n (by simp) h
    · rw [ih]
      constructor
      · intro H i hi
        rcases (lt_succ_iff_le.mp hi).lt_or_eq with hi | rfl
        · exact H i hi
        · exact h
      · intro H i hi
        exact H i (lt_trans hi (by simp))

@[simp]
lemma card_eq_zero_iff : card s = 0 ↔ s = ∅ := by
  rw [card, cardBelow_eq_zero_iff]
  constructor
  · intro h
    exact mem_ext fun i ↦ iff_of_false (fun hi ↦ h i (lt_of_mem hi) hi) (by simp)
  · rintro rfl
    simp

@[simp]
lemma card_empty : card (∅ : V) = 0 := card_eq_zero_iff.mpr rfl

end Arithmetic
end FFL.FirstOrder
