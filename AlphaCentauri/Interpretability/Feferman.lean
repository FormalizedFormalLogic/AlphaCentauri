module

public import AlphaCentauri.Interpretability.Henkin
public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.ToFoundation.ProvabilityAbstraction
public import Foundation.FirstOrder.Incompleteness.Second

/-!
# Feferman's theorem

The theory $T + \neg\mathrm{Con}_T$ is interpretable in $T$.

## References

- [Lin97, Theorem 6.8]
- [HP98, Lemma III.4.9]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment

variable (T : ArithmeticTheory) [T.Δ₁]

variable [𝗣𝗔 ⪯ T]

open Bootstrapping ProvabilityAbstraction

/-- $\mathsf{I}\Sigma_1$ proves that $\mathrm{Con}_T$ implies
$\mathrm{Con}_{T + \neg\mathrm{Con}_T}$.
- [HP98, Lemma III.4.9] -/
private lemma provable_consistent_imp_consistent_union_incon [𝗜𝚺₁ ⪯ T] :
    𝗜𝚺₁ ⊢ T.consistent.val 🡒 (T ∪ T.Incon).consistent.val := by
  have h₁ : 𝗜𝚺₁ ⊢ T.standardProvability.con 🡒
      ∼T.standardProvability (∼T.standardProvability.con 🡒 ⊥) :=
    formalized_not_con_unrefutable T.standardProvability
  apply complete.{0}
  intro (V : Type) _ _
  have e₁ := models_of_provable (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁) h₁
  simp only [Provability.con, Provability.pr, Semantics.Imp.models_imply,
    Semantics.Not.models_not, models_iff, Semiformula.eval_substs, Matrix.comp₁,
    Sentence.val_quote, Bounding.HierarchySymbol.Defined.iff, Fin.Fin1.eq_one, Fin.isValue,
    Matrix.cons_val_fin_one, consistent.defined] at e₁ ⊢
  intro hc hU
  have hq : (⌜∼T.consistent.val 🡒 ⊥⌝ : V) =
      imp ℒₒᵣ ⌜∼T.consistent.val⌝ ⌜(⊥ : ArithmeticSentence)⌝ := by
    simp [Sentence.quote_eq]
  have hp : Provable T (⌜∼T.consistent.val 🡒 ⊥⌝ : V) := by
    rw [hq, ← Derivation.provable_union_singleton_iff]
    exact hU
  exact e₁ hc hp

private lemma provable_consistent_union_incon : T ∪ T.Con ⊢ (T ∪ T.Incon).consistent.val := by
  have : 𝗜𝚺₁ ⪯ T := (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔).trans inferInstance
  have : 𝗜𝚺₁ ⪯ T ∪ T.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans inferInstance
  exact WeakerThan.pbl (provable_consistent_imp_consistent_union_incon T) ⨀ by_axm (by simp)

/-- Feferman's theorem: $T + \neg\mathrm{Con}_T$ is interpretable in $T$.

- [Lin97, Theorem 6.8]
- [HP98, Lemma III.4.9] -/
noncomputable abbrev interpretation_incon : T ⊳ T ∪ T.Incon := by
  have : 𝗣𝗔 ⪯ T ∪ T.Con :=
    (inferInstance : 𝗣𝗔 ⪯ T).trans (WeakerThan.ofSubset Set.subset_union_left)
  have : 𝗣𝗔 ⪯ T ∪ T.Incon :=
    (inferInstance : 𝗣𝗔 ⪯ T).trans (WeakerThan.ofSubset Set.subset_union_left)
  have hCon : T ∪ T.Con ⪯ insert T.consistent.val T :=
    WeakerThan.ofSubset (by rintro σ (hσ | rfl) <;> simp [*])
  have : 𝗣𝗔 ⪯ insert T.consistent.val T := (inferInstance : 𝗣𝗔 ⪯ T ∪ T.Con).trans hCon
  have : 𝗣𝗔 ⪯ insert (∼T.consistent.val) T :=
    (inferInstance : 𝗣𝗔 ⪯ T).trans (WeakerThan.ofSubset (Set.subset_insert _ _))
  have hw : T ∪ T.Con ∪ (T ∪ T.Incon).Con ⪯ insert T.consistent.val T :=
    WeakerThan.ofAxm! <| by
      rintro σ ((hσ | rfl) | rfl)
      · exact by_axm <| Set.mem_insert_of_mem _ hσ
      · exact by_axm (by simp)
      · exact WeakerThan.pbl (provable_consistent_union_incon T)
  have hU : T ∪ T.Incon ⪯ insert (∼T.consistent.val) T :=
    WeakerThan.ofSubset (by rintro σ (hσ | rfl) <;> simp [*])
  have h₁ : insert T.consistent.val T ⊳ T ∪ T.Incon :=
    (henkinInterpretation (T ∪ T.Incon) (T ∪ T.Con)).ofWeakerThanLeft
  have h₂ : insert (∼T.consistent.val) T ⊳ T ∪ T.Incon :=
    (DirectInterpretation.refl (T ∪ T.Incon)).ofWeakerThanLeft
  exact h₁.orCases T.consistent.val h₂

end FFL.FirstOrder.Arithmetic
