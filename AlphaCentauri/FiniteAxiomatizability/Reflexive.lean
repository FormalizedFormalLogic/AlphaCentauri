module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Incompleteness.Delta1
public import AlphaCentauri.FirstOrder.FiniteAxiomatizability

/-!
# Reflexive theories

A theory is reflexive if it proves the consistency of each of its finite subtheories. Every
reflexive extension of `𝗜𝚺₁` fails to be finitely axiomatizable.
-/

@[expose] public section

open LO.Entailment

namespace LO.FirstOrder

variable {T : ArithmeticTheory}

/-- `T` is reflexive if it proves the consistency of each of its finite subtheories `U`, presented
by `Theory.Δ₁.ofFinite`.
- [Lin97, Ch. 1 p. 18]
- [HP98, Definition III.2.32] -/
def ArithmeticTheory.Reflexive (T : ArithmeticTheory) : Prop :=
  ∀ U, U ⊆ T → (U_fin : U.Finite) →
    let _ : U.Δ₁ := Theory.Δ₁.ofFinite _ U_fin
    T ⊢ U.consistent.val

/-- `T` is essentially reflexive if every theory extending `T` is reflexive.
- [Lin97, Ch. 1 p. 18] -/
def ArithmeticTheory.EssentiallyReflexive (T : ArithmeticTheory) : Prop :=
  ∀ U : ArithmeticTheory, T ⊆ U → U.Reflexive

/-- A reflexive extension of `𝗜𝚺₁` is not finitely axiomatizable.

If a finite `F ⊆ T` axiomatized `T`, reflexivity would give `T ⊢ Con(F)`, hence `F ⊢ Con(F)`,
contradicting the second incompleteness theorem for `F`, which is `Δ₁`, contains `𝗜𝚺₁` and is
consistent. The finite subtheory is taken as a subset of `T` through
`finiteAxiomatizable_iff_exists_finite_subset`, and its `Theory.Δ₁` presentation is the one
`ArithmeticTheory.Reflexive` fixes, so that the consistency statement `T` proves is the one
`consistent_unprovable` speaks about.
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
theorem not_finiteAxiomatizable_of_reflexive [𝗜𝚺₁ ⪯ T] [Consistent T]
    (h : T.Reflexive) : ¬FiniteAxiomatizable T := by
  intro hfa
  obtain ⟨F, hFT, hfin, hequiv⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp hfa
  let _ : F.Δ₁ := Theory.Δ₁.ofFinite F hfin
  have hcon : T ⊢ F.consistent.val := h F hFT hfin
  have : 𝗜𝚺₁ ⪯ F := WeakerThan.trans inferInstance hequiv.symm.le
  have : Consistent F := Consistent.of_le inferInstance hequiv.le
  exact Arithmetic.consistent_unprovable F (hequiv.symm.le.wk hcon)

/-- `𝗜𝚺₂` proves the consistency of `𝗜𝚺₁`.

This is the `k = 1` case of the general fact that `𝗜𝚺 (k + 1)` proves the consistency of `𝗜𝚺 k`
for every `k`. The general statement needs a `(𝗜𝚺 k).Δ₁` instance for every `k`, but Foundation
currently only supplies `(𝗜𝚺 k).Δ₁` for `k = 1` (`ISigma1_delta1Definable` in
`Foundation.FirstOrder.Incompleteness.Delta1`; there is no such instance for a general `𝗜𝚺 k`),
so the statement here is restricted to the case that instance supports.
- [HP98, Corollary I.4.34(1)] -/
axiom ISigma.provable_con_ISigma1 : 𝗜𝚺 2 ⊢ (𝗜𝚺₁ : ArithmeticTheory).consistent.val

/-- `𝗣𝗔` is reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
axiom Peano.reflexive : (𝗣𝗔 : ArithmeticTheory).Reflexive

/-- `𝗣𝗔` is essentially reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
axiom Peano.essentiallyReflexive : (𝗣𝗔 : ArithmeticTheory).EssentiallyReflexive

/-- `𝗣𝗔` is not finitely axiomatizable.
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
axiom Peano.not_finiteAxiomatizable : ¬FiniteAxiomatizable (𝗣𝗔 : ArithmeticTheory)

/-- Every consistent extension of `𝗣𝗔` is not finitely axiomatizable.
- [Lin97, Corollary 2.1] -/
axiom not_finiteAxiomatizable_of_Peano_le [(𝗣𝗔 : ArithmeticTheory) ⪯ T] [Consistent T] :
    ¬FiniteAxiomatizable T

end LO.FirstOrder
