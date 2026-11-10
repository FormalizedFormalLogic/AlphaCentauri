module

public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.Syntax.Proof.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping.FixedPoint
public import Foundation.FirstOrder.Incompleteness.Reflection.Uniform

/-!
# Uniform reflection in models of $\mathsf{EA}$

A model of $\mathsf{EA}$ satisfies the uniform reflection schema of a theory `T` for `φ` iff every
instance of `φ` by numerals whose code is internally provable in `T` holds in the model, for
theories `T` whose axioms are locally $\Delta_0$ in the model.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.ElementaryArithmetic

open _root_.FFL.FirstOrder.Arithmetic.ElementaryArithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

lemma models_uniformReflectionSchema_iff (T : ArithmeticTheory) [T.Δ₁] [LocallyDelta0Axioms T V]
    {k : ℕ} (φ : ArithmeticSemisentence k) :
    V ⊧/![] (T.uniformReflectionSchema φ) ↔
      ∀ v : Fin k → V,
        Provable T (Bootstrapping.Arithmetic.substNumerals (((⌜φ⌝ : ℕ) : ℕ) : V) v) →
          V ⊧/v φ := by
  simp [Theory.uniformReflectionSchema, Sentence.quote_eq_encode, numeral_eq_natCast]

end FFL.FirstOrder.Arithmetic.ElementaryArithmetic
