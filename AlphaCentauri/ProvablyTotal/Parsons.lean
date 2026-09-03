module

public import AlphaCentauri.ProvablyTotal.Basic
public import AlphaCentauri.Computability.Vector

/-!
# Parsons' theorem

Parsons' theorem: the `𝗜𝚺₁`-provably total functions are exactly the primitive recursive
functions.

Both statements are recorded here with `sorry` bodies. Neither [HP98] nor [Lin97] nor [AB05]
contains a proof: the easy direction (`provablyTotal_of_primrec'`, primitive recursive functions
are `𝗜𝚺₁`-provably total) is [HP98, Theorem I.1.54], but the converse direction
(`primrec'_of_provablyTotal`) is only *stated*, at [HP98, Corollary IV.3.7], with a
model-theoretic proof sketch (via indicators and the Schwichtenberg–Wainer hierarchy) referencing
[HP98, Lemma IV.3.4], [HP98, Theorem IV.3.5] and [HP98, Corollary IV.3.34]; the alternative
proof-theoretic route (Parsons 1970, Mints 1971, Takeuti *Proof Theory*, Buss *Bounded
Arithmetic* (1986) §2.4 — free-cut elimination followed by finitary witness extraction) is only
mentioned in passing at [HP98, p. 245] and is developed in none of the three sources. See #6 for
the roadmap of what such a proof would need.
-/

@[expose] public section

namespace LO.FirstOrder

open LO.FirstOrder.Arithmetic

/-- Every primitive recursive function is `𝗜𝚺₁`-provably total.
- [HP98, Theorem I.1.54]
- [HP98, Lemma I.1.55]

Neither [HP98] nor [Lin97] nor [AB05] is cited for a proof here: this is the easy direction of
Parsons' theorem, `sorry`-bodied pending #15. -/
theorem provablyTotal_of_primrec' {k : ℕ} {f : List.Vector ℕ k → ℕ} (hf : Nat.Primrec' f) :
    𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) := sorry

/-- Every `𝗜𝚺₁`-provably total function is primitive recursive.

This is the hard direction of Parsons' theorem. [HP98, Corollary IV.3.7] states it but its proof
is not reproduced here (nor is it in [Lin97] or [AB05]); the proof-theoretic route (Parsons 1970,
Mints 1971, Takeuti, Buss — free-cut elimination and finitary witness extraction) is only
mentioned in passing at [HP98, p. 245]. `sorry`-bodied; see #6 for the proof roadmap. -/
theorem primrec'_of_provablyTotal {k : ℕ} {f : List.Vector ℕ k → ℕ}
    (hf : 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v))) : Nat.Primrec' f := sorry

/-- **Parsons' theorem**: the `𝗜𝚺₁`-provably total functions are exactly the primitive recursive
functions.
- [HP98, Corollary IV.3.7]

The statement is [HP98, Corollary IV.3.7], but neither its proof nor the proof-theoretic
alternative (Parsons 1970, Mints 1971, Takeuti, Buss — free-cut elimination and witness
extraction, mentioned only in passing at [HP98, p. 245]) is developed in [HP98], [Lin97] or
[AB05]; the two directions are recorded separately as `provablyTotal_of_primrec'` and
`primrec'_of_provablyTotal`, both `sorry`-bodied, and this statement is `sorry`-bodied
independently of them pending that proof. See #6 for the roadmap. -/
theorem parsons {k : ℕ} (f : List.Vector ℕ k → ℕ) :
    Nat.Primrec' f ↔ 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) := sorry

/-- The `Primrec` corollary of Parsons' theorem, via Mathlib's `Nat.Primrec'.prim_iff`
(`Nat.Primrec' f ↔ Primrec f` for `f : List.Vector ℕ k → ℕ`).
- [HP98, Corollary IV.3.7]

Same provenance and caveats as `parsons`; `sorry`-bodied pending #6. -/
theorem parsons_primrec {k : ℕ} (f : List.Vector ℕ k → ℕ) :
    Primrec f ↔ 𝗜𝚺₁.ProvablyTotal (fun v ↦ f (.ofFn v)) := sorry

end LO.FirstOrder
