module

public import Foundation.FirstOrder.Arithmetic.HFS.Basic

/-!
# Elementary facts about coded sets

Adding elements to a coded set.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

lemma bitRemove_insert_of_not_mem {x s : V} (h : x ∉ s) : bitRemove x (insert x s) = s :=
  mem_ext fun _ ↦ by grind

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
