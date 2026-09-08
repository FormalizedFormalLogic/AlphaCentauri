module

public import AlphaCentauri.Vorspiel.Primrec
public import AlphaCentauri.ProvablyTotal.Basic

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably total

Every primitive recursive function is `𝗜𝚺₁`-provably total, in Mathlib's `Nat.Primrec'` and
`Primrec` forms.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

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

end FFL.FirstOrder.Arithmetic
