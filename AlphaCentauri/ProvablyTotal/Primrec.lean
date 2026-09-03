module

public import AlphaCentauri.Vorspiel.Primrec
public import AlphaCentauri.ProvablyTotal.Basic

/-!
# Primitive recursive functions are `𝗜𝚺₁`-provably total

The easy direction of Parsons' theorem: every primitive recursive function is `𝗜𝚺₁`-provably
total, in both of Mathlib's forms — `Nat.Primrec'` on `List.Vector ℕ k → ℕ` and the curried
`Primrec` — translated to `(Fin k → ℕ) → ℕ` through `List.Vector.ofFn`, the same translation
`AlphaCentauri.Vorspiel.Primrec` uses for the `Nat.Primrec'`/`Primrec` bridge lemmas.

Both statements are recorded here with `sorry` bodies. The intended proof builds the `𝚺₁` graph
formula of `f` by induction on `Nat.Primrec' f`, using at the primitive-recursion step the
course-of-values construction of [HP98, Lemma I.1.55]; provable totality of the result is then
[HP98, Theorem I.1.54]. Foundation's `LO.FirstOrder.Arithmetic.PR.Construction` is the model-side
form of the Lemma I.1.55 construction: it packages a `zero`/`succ` step pair together with their
`𝚺₁`-definitions into a single primitive recursion over a model of `𝗜𝚺₁`.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

/-- Every primitive recursive function, in Mathlib's `List.Vector` form `Nat.Primrec'`, is
`𝗜𝚺₁`-provably total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyTotal_of_primrec' {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) := by
  sorry

/-- Every primitive recursive function, in Mathlib's curried form `Primrec`, is `𝗜𝚺₁`-provably
total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55] -/
theorem provablyTotal_of_primrec {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Primrec f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) := by
  sorry

end LO.FirstOrder.Arithmetic
