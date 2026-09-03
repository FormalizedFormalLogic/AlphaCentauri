module

public import Foundation.FirstOrder.Incompleteness.Second

/-!
# Reflexive theories

A theory is reflexive if it proves the consistency of each of its finite subtheories. Every
reflexive extension of `𝗜𝚺₁` fails to be finitely axiomatizable.
-/

@[expose] public section

open LO.Entailment

namespace LO.FirstOrder

variable {T : ArithmeticTheory}

/-- `T` is reflexive if, for every finite `l ⊆ T`, `T` proves the consistency of `l` (presented
via `Theory.Δ₁.ofList l.toList`).
- [Lin97, Ch. 1 p. 18] -/
def ArithmeticTheory.Reflexive (T : ArithmeticTheory) : Prop :=
  ∀ l : Finset ArithmeticSentence, (∀ σ ∈ l, σ ∈ T) →
    letI : Theory.Δ₁ {σ | σ ∈ l} := (Theory.Δ₁.ofList l.toList).ofEq (by ext; simp)
    T ⊢ (Theory.consistent {σ | σ ∈ l}).val

/-- `T` is essentially reflexive if every theory extending `T` is reflexive.
- [Lin97, Ch. 1 p. 18] -/
def ArithmeticTheory.EssentiallyReflexive (T : ArithmeticTheory) : Prop :=
  ∀ U : ArithmeticTheory, T ⊆ U → U.Reflexive

/-- A reflexive extension of `𝗜𝚺₁` is not finitely axiomatizable.
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
theorem not_finiteAxiomatizable_of_reflexive [𝗜𝚺₁ ⪯ T] [Consistent T]
    (h : T.Reflexive) : ¬FiniteAxiomatizable T := sorry

end LO.FirstOrder
