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

/-- `T` is reflexive if it proves the consistency of every finite subtheory.
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
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
theorem not_finiteAxiomatizable_of_reflexive [𝗜𝚺₁ ⪯ T] [Consistent T] (h : T.Reflexive) : ¬FiniteAxiomatizable T := by
  by_contra! hfa
  obtain ⟨F, hFT, hfin, hequiv⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp hfa
  let : F.Δ₁ := Theory.Δ₁.ofFinite F hfin
  have hcon : T ⊢ F.consistent.val := h F hFT hfin
  have : 𝗜𝚺₁ ⪯ F := WeakerThan.trans inferInstance hequiv.symm.le
  have : Consistent F := Consistent.of_le inferInstance hequiv.le
  exact Arithmetic.consistent_unprovable F (hequiv.symm.le.wk hcon)

/-- `𝗜𝚺₂` proves the consistency of `𝗜𝚺₁`.
- [HP98, Corollary I.4.34(1)] -/
axiom ISigma.provable_con_ISigma1 : 𝗜𝚺 2 ⊢ 𝗜𝚺₁.consistent.val

/-- `𝗣𝗔` is reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
axiom Peano.reflexive : 𝗣𝗔.Reflexive

/-- `𝗣𝗔` is essentially reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
axiom Peano.essentiallyReflexive : 𝗣𝗔.EssentiallyReflexive

/-- `𝗣𝗔` is not finitely axiomatizable.
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
theorem Peano.not_finiteAxiomatizable : ¬FiniteAxiomatizable 𝗣𝗔 :=
  not_finiteAxiomatizable_of_reflexive Peano.reflexive

/-- Every consistent extension of `𝗣𝗔` is not finitely axiomatizable.
- [Lin97, Corollary 2.1] -/
theorem not_finiteAxiomatizable_of_Peano_le [𝗣𝗔 ⪯ T] [Consistent T] : ¬FiniteAxiomatizable T := by
  have hR : (𝗣𝗔 ∪ T).Reflexive := Peano.essentiallyReflexive _ Set.subset_union_left
  have hUT : 𝗣𝗔 ∪ T ⪯ T := WeakerThan.ofAxm! <| by
    intro σ hσ
    rcases hσ with hσ | hσ
    · exact ‹𝗣𝗔 ⪯ T›.wk <| Axiomatized.by_axm hσ
    · exact Axiomatized.by_axm hσ
  have hequiv : T ≊ 𝗣𝗔 ∪ T := Equiv.antisymm_iff.mpr ⟨inferInstance, hUT⟩
  have : 𝗜𝚺₁ ⪯ 𝗣𝗔 ∪ T := WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔) inferInstance
  have : Consistent (𝗣𝗔 ∪ T) := Consistent.of_le ‹Consistent T› hUT
  exact mt (FiniteAxiomatizable.of_equiv hequiv) <| not_finiteAxiomatizable_of_reflexive hR

end LO.FirstOrder
