module

public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.NumberTheory.FLT3
public import AlphaCentauri.NumberTheory.Primes
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Mathlib.Computability.Halting

/-!
# What $\mathsf{IOpen}$ does not prove

Shepherdson's model of Puiseux polynomials over the real algebraic numbers with integer constant
term is a model of $\mathsf{IOpen}$ in which every irreducible element is standard. Together with
the models of Macintyre and Marker and of Adamowicz, and with Smith's open induction domains with
greatest common divisors, it shows that $\mathsf{IOpen}$ does not prove the infinitude of primes,
Euclid's lemma, or, over the existence of greatest common divisors, Bézout's theorem. It is not
finitely axiomatizable, and, unlike $\mathsf{PA}$ by Tennenbaum's theorem, it has a computable
nonstandard model.

- [She64]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding FFL.FirstOrder.Arithmetic

/-- Euclid's lemma: a prime dividing a product divides one of the factors. -/
def primeDvdMul : ArithmeticSentence := “∀ p a b, !isPrime p → p ∣ a * b → p ∣ a ∨ p ∣ b”

/-- Any two elements have a greatest common divisor. -/
def greatestCommonDivisor : ArithmeticSentence :=
  “∀ x y, ∃ z, z ∣ x ∧ z ∣ y ∧ ∀ w, w ∣ x → w ∣ y → w ∣ z”

/-- $\mathsf{IOpen}$ does not prove the infinitude of primes.
- [She64]
- [Wil78]
- [DAq05, §2, §3]
- [MM89]
- [Ada87] -/
axiom not_provable_infinitudeOfPrimes_IOpen : ¬𝗜𝗢𝗽𝗲𝗻 ⊢ infinitudeOfPrimes

/-- $\mathsf{IOpen}$ does not prove Euclid's lemma.
- [MM89]
- [DAq05, §2] -/
axiom not_provable_primeDvdMul_IOpen : ¬𝗜𝗢𝗽𝗲𝗻 ⊢ primeDvdMul

/-- $\mathsf{IOpen} + \mathrm{GCD}$ does not prove Bézout's theorem.
- [Smi93a]
- [Smi92b, §3]
- [Moh11, §2] -/
axiom not_provable_bezout_IOpen_greatestCommonDivisor :
    ¬insert greatestCommonDivisor 𝗜𝗢𝗽𝗲𝗻 ⊢ bezout

/-- $\mathsf{IOpen}$ is not finitely axiomatizable.
- [Bou91]
- [Moh11, Corollary E]
- [Kov24, Theorem 2.2] -/
axiom IOpen.not_finiteAxiomatizable : ¬FiniteAxiomatizable 𝗜𝗢𝗽𝗲𝗻

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
