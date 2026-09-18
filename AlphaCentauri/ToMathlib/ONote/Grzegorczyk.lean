module

public import AlphaCentauri.ToMathlib.ElementaryClosure
public import AlphaCentauri.ToMathlib.ONote.FastGrowing

/-!
# The extended Grzegorczyk hierarchy over `ONote`

`extendedGrzegorczyk o k` is the extended Grzegorczyk (fast-growing) hierarchy class `𝓔^o`: the
elementary closure of `{F_β | β < o}`, where `F_β` is `ONote.fastGrowing β`.
-/

@[expose] public section

namespace ONote

/-- The family, by arity, of the fast-growing functions `F_β` for `β < o`; empty away from
arity `1`.
- [Bek99, §6] -/
def fastGrowingFamily (o : ONote) : ∀ k, Set ((Fin k → ℕ) → ℕ)
  | 1 => {f | ∃ β < o, f = fun v : Fin 1 → ℕ ↦ fastGrowing β (v 0)}
  | _ => ∅

lemma fastGrowingFamily_mono {o o' : ONote} (h : o ≤ o') (k : ℕ) :
    fastGrowingFamily o k ⊆ fastGrowingFamily o' k := by
  rcases k with _ | _ | k
  · exact fun f hf ↦ hf.elim
  · rintro f ⟨β, hβ, rfl⟩; exact ⟨β, hβ.trans_le h, rfl⟩
  · exact fun f hf ↦ hf.elim

/-- The extended Grzegorczyk (fast-growing) hierarchy class `𝓔^o` at arity `k`: the elementary
closure of `{F_β | β < o}`.
- [Bek99, §6] -/
def extendedGrzegorczyk (o : ONote) (k : ℕ) : Set ((Fin k → ℕ) → ℕ) :=
  Nat.elementaryClosure (fastGrowingFamily o) k

lemma extendedGrzegorczyk_mono {o o' : ONote} (h : o ≤ o') (k : ℕ) :
    extendedGrzegorczyk o k ⊆ extendedGrzegorczyk o' k :=
  Nat.elementaryClosure_mono (fastGrowingFamily_mono h) k

end ONote
