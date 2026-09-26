module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

@[expose] public section
/-!
# Codes of sentences
-/

namespace FFL.FirstOrder.Sentence

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma shift_quote (σ : ArithmeticSentence) : shift ℒₒᵣ (⌜σ⌝ : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, ← Semiformula.quote_shift]
  simp

end FFL.FirstOrder.Sentence
