module

public import AlphaCentauri.OmegaLogic.Embedding

/-!
# The consistency of `𝗣𝗔`, read off `Z_∞`

The consistency of `𝗣𝗔` follows as a corollary of the `Z_∞` development in this directory.

**This is not new mathematics.** Foundation already has `instance : Entailment.Consistent 𝗣𝗔` in
`FirstOrder/Arithmetic/Schemata.lean`, proved directly from the soundness of first-order logic
over `ℕ`; the theorem below is that instance's statement with a longer proof. Its purpose is to be
an integration check on the `Z_∞` chain — every link is exercised, and the audit confirms the chain
leans on nothing but the three standard axioms.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

/-- **The consistency of `𝗣𝗔`, via `Z_∞`.** Foundation's `Entailment.Consistent 𝗣𝗔` says the same
thing by way of soundness over `ℕ`.

- [Tow20, Section 16] -/
theorem consistent_PA : 𝗣𝗔 ⊬ ⊥ := by
  intro h
  obtain ⟨d⟩ := (provable_iff_derivable2 (L := ℒₒᵣ) (T := 𝗣𝗔) (φ := ⊥)).mp h
  obtain ⟨α, hα⟩ := Provable.of_derivation2_cutFree d fun _ => 0
  exact Provable.not_empty (Provable.remove_falsum (by simpa using hα))

end LO.FirstOrder.Arithmetic.OmegaLogic
