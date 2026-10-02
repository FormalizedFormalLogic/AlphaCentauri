module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Codes of sentences and of closed arithmetic terms
-/

@[expose] public section

namespace FFL.FirstOrder.Sentence

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma shift_quote (σ : ArithmeticSentence) : shift ℒₒᵣ (⌜σ⌝ : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, ← Semiformula.quote_shift]
  simp

end FFL.FirstOrder.Sentence

namespace FFL.FirstOrder.Semiterm

open Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n : ℕ}

section

variable (w : Fin 0 → ClosedSemiterm ℒₒᵣ n)

@[simp] lemma empty_quote_func_zero :
    (⌜(func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = 𝟎 :=
  Arithmetic.coe_zero_eq.symm

@[simp] lemma empty_quote_func_one :
    (⌜(func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = 𝟏 :=
  Arithmetic.coe_one_eq.symm

end

section

variable (w : Fin 2 → ClosedSemiterm ℒₒᵣ n)

@[simp] lemma empty_quote_func_add :
    (⌜(func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = ⌜w 0⌝ ^+ ⌜w 1⌝ :=
  rfl

@[simp] lemma empty_quote_func_mul :
    (⌜(func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ n)⌝ : V) = ⌜w 0⌝ ^* ⌜w 1⌝ :=
  rfl

end

end FFL.FirstOrder.Semiterm
