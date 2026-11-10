module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.NumberTheory.FLT3
public import AlphaCentauri.NumberTheory.Primes
public import Mathlib.Computability.Halting

/-!
# What $\mathsf{IOpen}$ does not prove

Statements about the first-order theory $\mathsf{IOpen}$ of induction for open formulas: it does not
prove the infinitude of primes, Euclid's lemma, or Bézout's theorem over the existence of greatest
common divisors, and it has a computable nonstandard model.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- Euclid's lemma: a prime dividing a product divides one of the factors. -/
def primeDvdMul : ArithmeticSentence := “∀ p a b, !isPrime p → p ∣ a * b → p ∣ a ∨ p ∣ b”

/-- Any two elements have a greatest common divisor. -/
def greatestCommonDivisor : ArithmeticSentence :=
  “∀ x y, ∃ z, z ∣ x ∧ z ∣ y ∧ ∀ w, w ∣ x → w ∣ y → w ∣ z”

/-- - [She64]
- [Wil78]
- [DAq05, §2, §3]
- [MM89]
- [Ada87] -/
axiom not_provable_infinitudeOfPrimes_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊬ infinitudeOfPrimes

/-- - [MM89]
- [DAq05, §2] -/
axiom not_provable_primeDvdMul_IOpen : 𝗜𝗢𝗽𝗲𝗻 ⊬ primeDvdMul

/-- $\mathsf{IOpen}$ with greatest common divisors does not prove Bézout's theorem.
- [Smi93a]
- [Smi92b, §3]
- [Moh11, §2] -/
axiom not_provable_bezout_IOpen_greatestCommonDivisor :
    insert greatestCommonDivisor 𝗜𝗢𝗽𝗲𝗻 ⊬ bezout

/-- $\mathsf{IOpen}$ has a nonstandard model, on the type $\mathbb{N}$ up to a bijection, whose
addition, multiplication and order are computable.
- [She64]
- [BO96, §1] -/
axiom exists_computable_nonstandard_model_IOpen :
    ∃ (M : Type) (_ : ORingStructure M) (e : M ≃ ℕ),
      Computable₂ (fun a b : ℕ ↦ e (e.symm a + e.symm b)) ∧
      Computable₂ (fun a b : ℕ ↦ e (e.symm a * e.symm b)) ∧
      ComputablePred (fun p : ℕ × ℕ ↦ e.symm p.1 < e.symm p.2) ∧
      M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 ∧
      ∃ a : M, ∀ n : ℕ, M ⊧/![a] (“x. ↑n < x” : ArithmeticSemisentence 1)

end FFL.FirstOrder.Arithmetic
