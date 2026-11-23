module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Coding
public import Mathlib.Combinatorics.Colex

/-!
# Codes of lists and finite sets in `ℕ`

In `ℕ`, the vector coding a list is `Encodable.encode` of the list, and the set coded by
$\sum_{i \in S} 2^i$ is $S$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Encodable

lemma encode_list_cons_eq_adjoin (x : ℕ) (l : List ℕ) : encode (x :: l) = x ∷ encode l := by
  simp [adjoin_def, nat_pair_eq]

@[simp] lemma len_encode_list (l : List ℕ) : len (encode l) = l.length := by
  induction l with
  | nil => simp [encode_list_nil]
  | cons x l ih => rw [encode_list_cons_eq_adjoin]; simp [ih]

@[simp] lemma nth_encode_list (l : List ℕ) (i : ℕ) : (encode l).[i] = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [encode_list_nil]
  | cons x l ih => rw [encode_list_cons_eq_adjoin]; cases i <;> simp [ih]

lemma mem_sum_two_pow_iff {x : ℕ} {S : Finset ℕ} : x ∈ (∑ i ∈ S, 2 ^ i : ℕ) ↔ x ∈ S := by
  rw [Bootstrapping.mem_iff_mem_bitIndices, ← List.mem_toFinset, ← Finset.equivBitIndices_apply,
    ← Finset.equivBitIndices_symm_apply, Equiv.apply_symm_apply]

end FFL.FirstOrder.Arithmetic
