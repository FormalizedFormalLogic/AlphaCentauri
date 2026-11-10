module

public import Foundation.Vorspiel.Computability.Primrec

/-!
# Primitive recursion for vector encodings

The correspondence between `Fin k → ℕ` and `List.Vector ℕ k` argument forms.
-/

@[expose] public section

section vector

variable {k : ℕ}

theorem PrimrecPred.comp_get_iff {p : (Fin k → ℕ) → Prop} :
    PrimrecPred (fun v : List.Vector ℕ k ↦ p v.get) ↔ PrimrecPred p :=
  ⟨fun h ↦ (h.comp Primrec.vector_ofFn').of_eq fun v ↦ by
      rw [funext (List.Vector.get_ofFn v)], fun h ↦ h.comp Primrec.vector_get'⟩

end vector
