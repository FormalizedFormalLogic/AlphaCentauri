module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Incompleteness.Delta1

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

/-- `𝗜𝚺₂` proves the consistency of `𝗜𝚺₁`.

This is the `k = 1` case of the general fact that `𝗜𝚺 (k + 1)` proves the consistency of `𝗜𝚺 k`
for every `k`. The general statement needs a `(𝗜𝚺 k).Δ₁` instance for every `k`, but Foundation
currently only supplies `(𝗜𝚺 k).Δ₁` for `k = 1` (`ISigma1_delta1Definable` in
`Foundation.FirstOrder.Incompleteness.Delta1`; there is no such instance for a general `𝗜𝚺 k`),
so the statement here is restricted to the case that instance supports.
- [HP98, Corollary I.4.34(1)] -/
theorem ISigma.provable_con_ISigma1 : 𝗜𝚺 2 ⊢ (𝗜𝚺₁ : ArithmeticTheory).consistent.val := sorry

/-- `𝗣𝗔` is reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
theorem Peano.reflexive : (𝗣𝗔 : ArithmeticTheory).Reflexive := sorry

/-- `𝗣𝗔` is essentially reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
theorem Peano.essentiallyReflexive : (𝗣𝗔 : ArithmeticTheory).EssentiallyReflexive := sorry

/-- `𝗣𝗔` is not finitely axiomatizable.
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
theorem Peano.not_finiteAxiomatizable : ¬FiniteAxiomatizable (𝗣𝗔 : ArithmeticTheory) := sorry

/-- Every consistent extension of `𝗣𝗔` is not finitely axiomatizable.
- [Lin97, Corollary 2.1] -/
theorem not_finiteAxiomatizable_of_Peano_le [(𝗣𝗔 : ArithmeticTheory) ⪯ T] [Consistent T] :
    ¬FiniteAxiomatizable T := sorry

end LO.FirstOrder
