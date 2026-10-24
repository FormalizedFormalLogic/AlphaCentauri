module

public import Foundation.Vorspiel.Matrix
public import Mathlib.Data.Vector.Basic

/-!
# Vectors and functions on `Fin`

Companion of Mathlib's `List.Vector.tail_ofFn`, `List.Vector.head_ofFn` and `Fin.append_right`.
-/

@[expose] public section

namespace List.Vector

variable {α : Type*} {n : ℕ}

@[simp] lemma ofFn_cons (a : α) (f : Fin n → α) : ofFn (a :> f) = a ::ᵥ ofFn f := by simp [ofFn]

end List.Vector

namespace Fin

lemma append_addCast {α : Type*} {k : ℕ} (s u : Fin k → α) (i : Fin k) :
    Fin.append s u (Fin.addCast k i) = s i := by
  simp [Fin.addCast]

lemma append_addNat {α : Type*} {k : ℕ} (s u : Fin k → α) (i : Fin k) :
    Fin.append s u (i.addNat k) = u i := by
  have : i.addNat k = Fin.natAdd k i := Fin.ext (Nat.add_comm _ _)
  rw [this, Fin.append_right]

end Fin
