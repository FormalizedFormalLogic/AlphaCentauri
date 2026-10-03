module

public import Foundation.FirstOrder.Arithmetic.HFS.Basic

/-!
# Elementary facts about coded sets

Adding elements to a coded set.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma insert_comm (x y s : V) : insert x (insert y s) = insert y (insert x s) := by
  apply mem_ext
  intro z
  simp only [mem_bitInsert_iff]
  tauto

lemma insert_insert_self (x s : V) : insert x (insert x s) = insert x s := by
  apply mem_ext
  intro z
  simp only [mem_bitInsert_iff]
  tauto

lemma mem_of_mem_insert_of_ne {x y s : V} (h : x ∈ insert y s) (hne : x ≠ y) : x ∈ s :=
  (mem_bitInsert_iff.mp h).resolve_left hne

lemma insert_subset_insert_insert {a p Γ s : V} (h : Γ ⊆ insert p s) :
    insert a Γ ⊆ insert p (insert a s) := by
  intro x hx
  rcases mem_bitInsert_iff.mp hx with rfl | hx
  · simp
  · rcases mem_bitInsert_iff.mp (h hx) with rfl | hx
    · simp
    · simp [hx]

end FFL.FirstOrder.Arithmetic
