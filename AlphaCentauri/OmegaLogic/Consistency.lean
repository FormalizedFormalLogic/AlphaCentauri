module

public import AlphaCentauri.OmegaLogic.Embedding

/-!
# The consistency of `𝗣𝗔`, read off `Z_∞`

This file states the consistency of `𝗣𝗔` as a consequence of the `Z_∞` development.

Neither [HP98] nor [Lin97] treats ω-logic; the presentation followed is [Tow20].
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.OmegaLogic

/-- Peano arithmetic does not prove falsity.

- [Tow20, Section 16] -/
theorem consistent_PA : 𝗣𝗔 ⊬ ⊥ := by
  intro h
  obtain ⟨d⟩ := (provable_iff_derivable2 (L := ℒₒᵣ) (T := 𝗣𝗔) (φ := ⊥)).mp h
  obtain ⟨α, hα⟩ := Provable.of_derivation2_cutFree d fun _ => 0
  exact Provable.not_empty (Provable.remove_falsum (by simpa using hα))

end LO.FirstOrder.Arithmetic.OmegaLogic
