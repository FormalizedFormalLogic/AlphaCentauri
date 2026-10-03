module

public import Foundation.Vorspiel.Computability.Primrec

/-!
# Primitive recursion for vector encodings

The correspondence between `Fin k → ℕ` and `List.Vector ℕ k` argument forms.
-/

@[expose] public section

section vector

variable {k : ℕ}

theorem Nat.Primrec'.comp_get_iff {f : (Fin k → ℕ) → ℕ} :
    Nat.Primrec' (fun v : List.Vector ℕ k ↦ f v.get) ↔ Primrec f := by
  rw [Nat.Primrec'.prim_iff]
  exact ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

theorem Nat.Primrec'.comp_ofFn_iff {f : List.Vector ℕ k → ℕ} :
    Primrec (fun v : Fin k → ℕ ↦ f (List.Vector.ofFn v)) ↔ Nat.Primrec' f := by
  rw [Nat.Primrec'.prim_iff]
  exact ⟨fun h ↦ (h.comp Primrec.vector_get').of_eq (by simp [List.Vector.ofFn_get]),
    fun h ↦ h.comp Primrec.vector_ofFn'⟩

theorem PrimrecPred.comp_get_iff {p : (Fin k → ℕ) → Prop} :
    PrimrecPred (fun v : List.Vector ℕ k ↦ p v.get) ↔ PrimrecPred p :=
  ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

end vector
