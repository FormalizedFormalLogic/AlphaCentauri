module

public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex

/-!
# Prenex sentences of a given level over $\mathsf{I}\Sigma_1$

Companion of Foundation's `Arithmetic/ISigma1/Prenex.lean`. Every prenex class contains a sentence
refutable in $\mathsf{I}\Sigma_1$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.ISigma1

lemma exists_prenexHierarchy_refutable (Γ : Polarity) (n : ℕ) :
    ∃ χ : ArithmeticSentence, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ n χ ∧ 𝗜𝚺₁ ⊢ ∼χ := by
  use (Bounding.Prenex.falsum : ℬ[<, ℒₒᵣ].Prenex Γ n Empty 0).val;
  and_intros;
  · exact Bounding.Prenex.val_prenexHierarchy;
  · apply complete;
    intro (V : Type) _ _;
    simp [models_iff, Bounding.Prenex.models_falsum]

end FFL.FirstOrder.Arithmetic.ISigma1

end
