module

public import AlphaCentauri.OmegaLogic.Embedding
public import AlphaCentauri.OmegaLogic.CutElimination.Reduction

/-!
# Consistency of `𝗣𝗔` in `Z_∞`

`𝗣𝗔` does not prove falsity.

- [Tow20, Section 16]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic
namespace OmegaLogic

/-- Peano arithmetic does not prove falsity.

- [Tow20, Section 16] -/
theorem consistent_PA : 𝗣𝗔 ⊬ ⊥ := by
  intro h
  obtain ⟨d⟩ := (provable_iff_derivable2 (L := ℒₒᵣ) (T := 𝗣𝗔) (φ := ⊥)).mp h
  obtain ⟨α, hα⟩ := Provable.of_derivation2_cutFree d fun _ => 0
  exact Provable.not_empty (Provable.remove_falsum (by simpa using hα))

end OmegaLogic
end FFL.FirstOrder.Arithmetic
