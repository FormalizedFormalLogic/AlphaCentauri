module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Incompleteness.Definability
public import AlphaCentauri.Axiomatizability.Basic
public import AlphaCentauri.Bootstrapping.Proof.ComplexitySoundness
public import AlphaCentauri.Bootstrapping.Proof.LocalReflection

/-!
# Reflexive theories

A theory is reflexive if it proves the consistency of each of its finite subtheories. Every
reflexive extension of `𝗜𝚺₁` fails to be finitely axiomatizable.
-/

@[expose] public section

open FFL.Entailment

namespace FFL.FirstOrder

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

lemma ArithmeticTheory.EssentiallyReflexive.reflexive {T : ArithmeticTheory}
    (h : T.EssentiallyReflexive) : T.Reflexive :=
  h T Set.Subset.rfl

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic

variable {T : ArithmeticTheory}

/-- A reflexive extension of `𝗜𝚺₁` is not finitely axiomatizable.
- [Lin97, Corollary 2.1]
- [HP98, Corollary III.2.24] -/
theorem not_finiteAxiomatizable_of_reflexive [𝗜𝚺₁ ⪯ T] [Consistent T] (h : T.Reflexive) :
    ¬FiniteAxiomatizable T := by
  by_contra! hfa
  obtain ⟨F, hFT, hfin, hequiv⟩ := finiteAxiomatizable_iff_exists_finite_subset.mp hfa
  let : F.Δ₁ := Theory.Δ₁.ofFinite F hfin
  have hcon : T ⊢ F.consistent.val := h F hFT hfin
  have : 𝗜𝚺₁ ⪯ F := WeakerThan.trans inferInstance hequiv.le
  have : Consistent F := Consistent.of_le inferInstance hequiv.symm.le
  exact consistent_unprovable F (hequiv.le.wk hcon)

/-- `𝗜𝚺₂` proves the consistency of `𝗜𝚺₁`.
- [HP98, Corollary I.4.34(1)] -/
theorem ISigma.provable_con_ISigma1 : 𝗜𝚺 2 ⊢ 𝗜𝚺₁.consistent.val := by
  apply Arithmetic.complete.{0} (𝗜𝚺 2) _
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁ := mod_IBroadSigma_of_le (s₂ := 2) (by simp)
  exact (Bootstrapping.consistent.defined _).mpr <|
    Bootstrapping.consistent_ISigma (k := 1) le_rfl

open Bootstrapping in
/-- In a model of `𝗣𝗔`, a finite set of true sentences is consistent.
- [HP98, Corollary I.4.34] -/
private lemma Peano.consistent_of_models {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (U : ArithmeticTheory) (hU : U.Finite) (h : ∀ σ ∈ U, V↓[ℒₒᵣ] ⊧ σ) :
    let _ : U.Δ₁ := Theory.Δ₁.ofFinite U hU
    U.Consistent V := by
  intro _ hp
  let l := hU.toFinset.toList
  have hl : ∀ σ ∈ l, V↓[ℒₒᵣ] ⊧ σ := by simpa [l] using h
  have hd := Derivation.provable_deduction (V := V) l hp
  let N := hU.toFinset.sup fun σ : ArithmeticSentence ↦ σ.complexity
  have hN : ∀ σ ∈ l, σ.complexity ≤ N := fun σ hσ ↦
    Finset.le_sup (f := fun σ : ArithmeticSentence ↦ σ.complexity) (by simpa [l] using hσ)
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺(N + 1) := ModelsTheory.of_provably_subtheory V _ 𝗣𝗔 inferInstance
  obtain ⟨σ, hσ, hmodel⟩ := hd.exists_models (N := N) fun r hr ↦ by
    rcases mem_bitInsert_iff.mp hr with rfl | hr
    · exact ⟨⊥, by simp, rfl⟩
    · obtain ⟨φ, hφ, rfl⟩ := LK2.Derivation.Sequent.mem_quote_iff'.mp hr
      simp only [Derivation.negatedAxioms, List.mem_toFinset, Finset.mem_image] at hφ
      obtain ⟨τ, hτ, rfl⟩ := hφ
      exact ⟨∼τ, by simpa using hN τ hτ, by simp [Sentence.quote_def]⟩
  have hσ' := LK2.Derivation.Sequent.mem_quote_iff.mp (by simpa [Sentence.quote_def] using hσ :
    (⌜(σ : Proposition ℒₒᵣ)⌝ : V) ∈
      (⌜insert (⊥ : Proposition ℒₒᵣ) (Derivation.negatedAxioms l)⌝ : V))
  simp only [Derivation.negatedAxioms, Finset.mem_insert, List.mem_toFinset,
    Finset.mem_image] at hσ'
  rcases hσ' with hσ' | ⟨τ, hτ, hτσ⟩
  · obtain rfl : σ = ⊥ := by simpa using hσ'
    simp at hmodel
  · obtain rfl : σ = ∼τ := Rewriting.emb_injective (by simpa using hτσ.symm)
    simp [hl τ hτ] at hmodel

/-- `𝗣𝗔` is essentially reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
theorem Peano.essentiallyReflexive : 𝗣𝗔.EssentiallyReflexive := by
  intro U hPA W hW hfin
  let _ : W.Δ₁ := Theory.Δ₁.ofFinite W hfin
  have : 𝗣𝗔 ⪯ U := WeakerThan.ofSubset hPA
  apply Arithmetic.complete.{0} U _
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ModelsTheory.of_provably_subtheory V 𝗣𝗔 U inferInstance
  exact (Bootstrapping.consistent.defined W).mpr <|
    Peano.consistent_of_models (V := V) W hfin fun σ hσ ↦ Theory.models V U (hW hσ)

/-- `𝗣𝗔` is reflexive.
- [Lin97, Corollary 1.8]
- [HP98, Theorem III.2.35] -/
theorem Peano.reflexive : 𝗣𝗔.Reflexive := Peano.essentiallyReflexive.reflexive

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

end FFL.FirstOrder.Arithmetic
