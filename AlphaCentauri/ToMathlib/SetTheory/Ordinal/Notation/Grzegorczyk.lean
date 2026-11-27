module

public import AlphaCentauri.ToMathlib.Computability.ElementaryClosure
public import AlphaCentauri.ToMathlib.SetTheory.Ordinal.Notation.FastGrowing

/-!
# The extended Grzegorczyk hierarchy over `ONote`
-/

@[expose] public section

namespace ONote

section
variable (o : ONote)

/-- The family, by arity, of the fast-growing functions `F_β` for `β < o`; empty away from
arity `1`.
- [Bek99, §6] -/
def fastGrowingFamily : ∀ k, Set ((Fin k → ℕ) → ℕ)
  | 1 => {f | ∃ β < o, f = fun v : Fin 1 → ℕ ↦ fastGrowing β (v 0)}
  | _ => ∅

/-- The extended Grzegorczyk (fast-growing) hierarchy class `𝓔^o` at arity `k`: the elementary
closure of `{F_β | β < o}`.
- [Bek99, §6] -/
def extendedGrzegorczyk (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  Nat.elementaryClosure (fastGrowingFamily o) k

end

section
variable {o o' : ONote} (h : o ≤ o') (k : ℕ)

include h in
lemma fastGrowingFamily_mono : fastGrowingFamily o k ⊆ fastGrowingFamily o' k := by
  rcases k with _ | _ | k
  · intro f hf
    exact hf.elim
  · rintro f ⟨β, hβ, rfl⟩
    exact ⟨β, hβ.trans_le h, rfl⟩
  · intro f hf
    exact hf.elim

include h in
lemma extendedGrzegorczyk_mono : extendedGrzegorczyk o k ⊆ extendedGrzegorczyk o' k :=
  Nat.elementaryClosure_mono (fastGrowingFamily_mono h) k

end

end ONote
