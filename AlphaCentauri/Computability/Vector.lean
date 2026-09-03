module

public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Primitive recursion across the Mathlib–Foundation boundary

Mathlib states primitive recursion on `ℕ`-vectors as `Nat.Primrec' : (List.Vector ℕ k → ℕ) → Prop`,
whereas Foundation's definability API works with `(Fin k → ℕ) → ℕ`. This file translates between
the two, and proves that the truth of a `Δ₀` formula is primitive recursive — the primitive
recursive counterpart of Foundation's `sigma1_re`.
-/

@[expose] public section

open LO.FirstOrder LO.FirstOrder.Arithmetic

section quantifier

variable {β : Type*} [Primcodable β] {R : ℕ → β → Prop}

/-- Bounded existential quantification over the first argument of a primitive recursive relation.
Mathlib's `PrimrecRel.exists_lt` is the case `β = ℕ`.

This is a routine strengthening of a Mathlib lemma and has no counterpart in the literature. -/
theorem PrimrecRel.exists_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (PrimrecRel.exists_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

/-- Bounded universal quantification over the first argument of a primitive recursive relation.
Mathlib's `PrimrecRel.forall_lt` is the case `β = ℕ`.

This is a routine strengthening of a Mathlib lemma and has no counterpart in the literature. -/
theorem PrimrecRel.forall_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (PrimrecRel.forall_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

end quantifier

/-- A constant predicate is primitive recursive.

This is a routine Mathlib-style closure lemma and has no counterpart in the literature. -/
theorem PrimrecPred.const {α : Type*} [Primcodable α] (p : Prop) : PrimrecPred fun _ : α ↦ p := by
  classical
  exact Primrec.primrecPred (Primrec.const (decide p))

section vector

variable {k : ℕ}

/-- A function on `Fin k → ℕ` is primitive recursive iff its `List.Vector` form is.

This is a routine bridge between two Mathlib encodings and has no counterpart in the literature. -/
theorem Nat.Primrec'.comp_get_iff {f : (Fin k → ℕ) → ℕ} :
    Nat.Primrec' (fun v : List.Vector ℕ k ↦ f v.get) ↔ Primrec f := by
  rw [Nat.Primrec'.prim_iff]
  exact ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

/-- A function on `List.Vector ℕ k` is primitive recursive iff its `Fin k → ℕ` form is.

This is a routine bridge between two Mathlib encodings and has no counterpart in the literature. -/
theorem Nat.Primrec'.comp_ofFn_iff {f : List.Vector ℕ k → ℕ} :
    Primrec (fun v : Fin k → ℕ ↦ f (List.Vector.ofFn v)) ↔ Nat.Primrec' f := by
  rw [Nat.Primrec'.prim_iff]
  exact ⟨fun h ↦ (h.comp Primrec.vector_get').of_eq (by simp [List.Vector.ofFn_get]),
    fun h ↦ h.comp Primrec.vector_ofFn'⟩

/-- A predicate on `Fin k → ℕ` is primitive recursive iff its `List.Vector` form is.

This is a routine bridge between two Mathlib encodings and has no counterpart in the literature. -/
theorem PrimrecPred.comp_get_iff {p : (Fin k → ℕ) → Prop} :
    PrimrecPred (fun v : List.Vector ℕ k ↦ p v.get) ↔ PrimrecPred p :=
  ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

end vector

namespace LO.FirstOrder.Arithmetic

variable {ξ : Type*} (ε : ξ → ℕ)

/-- The truth of a `Δ₀` formula is primitive recursive. This is the `Δ₀` counterpart of
Foundation's `sigma1_re`.
- [HP98, Theorem 0.35] -/
lemma deltaZero_primrec :
    (k : ℕ) → (φ : ArithmeticSemiformula ξ k) → Hierarchy 𝚺 0 φ →
      PrimrecPred fun v : List.Vector ℕ k ↦ φ.Eval v.get ε
  |              _, _, Hierarchy.verum _ _ _ => by simpa using PrimrecPred.const True
  |             _, _, Hierarchy.falsum _ _ _ => by simpa using PrimrecPred.const False
  |  _, _, Hierarchy.rel _ _ Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Hierarchy.nrel _ _ Language.Eq.eq v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.eq.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  |  _, _, Hierarchy.rel _ _ Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))
  | _, _, Hierarchy.nrel _ _ Language.LT.lt v => by
    simpa [← Matrix.fun_eq_vec_two]
      using (Primrec.nat_lt.comp (term_primrec (v 0)) (term_primrec (v 1))).not
  |                  _, _, Hierarchy.and hφ hψ => by
    simpa using (deltaZero_primrec _ _ hφ).and (deltaZero_primrec _ _ hψ)
  |                   _, _, Hierarchy.or hφ hψ => by
    simpa using (deltaZero_primrec _ _ hφ).or (deltaZero_primrec _ _ hψ)
  |       n, _, Hierarchy.ball (φ := φ) pt hφ => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (deltaZero_primrec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.forall_lt' h).comp (term_primrec t) .id
  |       n, _, Hierarchy.bexs (φ := φ) pt hφ => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    have h : PrimrecRel fun (x : ℕ) (v : List.Vector ℕ n) ↦ φ.Eval (x ::ᵥ v).get ε :=
      (deltaZero_primrec _ _ hφ).comp Primrec.vector_cons
    simpa [List.Vector.cons_get] using (PrimrecRel.exists_lt' h).comp (term_primrec t) .id

/-- The truth of a `Δ₀` formula, in the `Fin k → ℕ` form of Foundation's definability API.
- [HP98, Theorem 0.35] -/
lemma deltaZero_primrec' {k} {φ : ArithmeticSemiformula ξ k} (hφ : Hierarchy 𝚺 0 φ) :
    PrimrecPred fun v : Fin k → ℕ ↦ φ.Eval v ε :=
  PrimrecPred.comp_get_iff.mp (deltaZero_primrec ε k φ hφ)

end LO.FirstOrder.Arithmetic
