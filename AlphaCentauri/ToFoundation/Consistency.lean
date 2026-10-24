module

public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.ToFoundation.ProvabilityAbstraction
public import Foundation.FirstOrder.Incompleteness.Second

/-!
# Formalized consistency statements

The consistency of $T + \neg\mathrm{Con}_T$ from $\mathrm{Con}_T$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping FFL.Entailment ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- $\mathsf{I}\Sigma_1$ proves that $\mathrm{Con}_T$ implies
$\mathrm{Con}_{T + \neg\mathrm{Con}_T}$.
- [HP98, Lemma III.4.9] -/
theorem provable_consistent_imp_consistent_union_incon :
    𝗜𝚺₁ ⊢ T.consistent.val 🡒 (T ∪ T.Incon).consistent.val := by
  have h₁ : 𝗜𝚺₁ ⊢ T.standardProvability.con 🡒
      ∼T.standardProvability (∼T.standardProvability.con 🡒 ⊥) :=
    formalized_con_unrefutable T.standardProvability
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

end FFL.FirstOrder.Arithmetic
