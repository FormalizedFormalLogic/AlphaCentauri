module

public import Mathlib.Data.List.Sort

/-!
# Lists read through `List.getD`

Membership, inclusion and strict monotonicity of a list, stated through `List.getD` at the indices
below its length.
-/

@[expose] public section

namespace List

variable {α : Type*} {l t : List α} (d : α)

lemma forall_mem_iff_getD {P : α → Prop} : (∀ x ∈ l, P x) ↔ ∀ i < l.length, P (l.getD i d) := by
  rw [forall_mem_iff_getElem]
  exact forall₂_congr fun i hi ↦ by simp [hi]

lemma subset_iff_getD : t ⊆ l ↔ ∀ i < t.length, ∃ j < l.length, t.getD i d = l.getD j d := by
  rw [subset_def, forall_mem_iff_getD d]
  refine forall₂_congr fun i hi ↦ ?_
  simp only [mem_iff_getElem]
  constructor <;> rintro ⟨j, hj, h⟩ <;> exact ⟨j, hj, by simpa [hi, hj] using h.symm⟩

lemma sortedLT_iff_getD_lt_getD [Preorder α] :
    l.SortedLT ↔ ∀ j < l.length, ∀ i < j, l.getD i d < l.getD j d := by
  rw [sortedLT_iff_pairwise, pairwise_iff_getElem]
  constructor
  · intro h j hj i hij
    simpa [hj, hij.trans hj] using h i j (hij.trans hj) hj hij
  · intro h i j hi hj hij
    simpa [hi, hj] using h j hj i hij

end List
