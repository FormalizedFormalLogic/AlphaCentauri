module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
# The union of a list of coded sets

`listUnion v` is the union of the coded sets listed in the vector `v`.
-/

@[expose] public section

namespace FFL.FirstOrder
namespace Arithmetic

open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

open ListUnion

/-- The union of the coded sets listed in the vector `v`. -/
noncomputable def listUnion (v : V) : V := construction.result ![] v

@[simp] lemma listUnion_nil : listUnion (0 : V) = ∅ := by simp [listUnion, construction]

@[simp] lemma listUnion_adjoin (x v : V) : listUnion (x ∷ v) = x ∪ listUnion v := by
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

@[simp] lemma mem_listUnion_iff {x v : V} : x ∈ listUnion v ↔ ∃ i < len v, x ∈ v.[i] := by
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

lemma listUnion_eq_empty_iff {v : V} : listUnion v = ∅ ↔ ∀ i < len v, v.[i] = ∅ := by
  simp only [mem_ext_iff, mem_listUnion_iff, not_mem_empty, iff_false, not_exists, not_and]
  exact ⟨fun h i hi x hx ↦ h x i hi hx, fun h x i hi hx ↦ h i hi x hx⟩

end Arithmetic
end FFL.FirstOrder
