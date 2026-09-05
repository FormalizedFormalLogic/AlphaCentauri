module

public import AlphaCentauri.Vorspiel.Primrec
public import AlphaCentauri.ProvablyTotal.Basic

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably total

The easy direction of Parsons' theorem: every primitive recursive function is `𝗜𝚺₁`-provably
total, in both of Mathlib's forms — `Nat.Primrec'` on `List.Vector ℕ k → ℕ` and the curried
`Primrec` — translated to `(Fin k → ℕ) → ℕ` through `List.Vector.ofFn`, the same translation
`AlphaCentauri.Vorspiel.Primrec` uses for the `Nat.Primrec'`/`Primrec` bridge lemmas.

Both statements are recorded here as axioms; see [HP98, Theorem I.1.54] and
[HP98, Lemma I.1.55].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
axiom provablyTotal_of_primrec' {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
axiom provablyTotal_of_primrec {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))

end LO.FirstOrder.Arithmetic
