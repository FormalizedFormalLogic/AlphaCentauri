module

public import AlphaCentauri.Bootstrapping.Completeness.HenkinOperators
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.SententialAxioms

/-!
# The Henkin translation

The translation of a language $L$ into arithmetic given by the Henkin set of a theory $S$, over
any arithmetical theory containing $\mathsf{PA}$ and the consistency of $S$.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

instance : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ S.Con :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ T) (inferInstance : T ⪯ T ∪ S.Con)

instance : 𝗣𝗔 ⪯ T ∪ S.Con :=
  Entailment.WeakerThan.trans (inferInstance : 𝗣𝗔 ⪯ T) (inferInstance : T ⪯ T ∪ S.Con)

section models

omit [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] [L.Eq] [𝗣𝗔 ⪯ T] in
lemma consistent_of_models_con {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    [V↓[ℒₒᵣ] ⊧* T ∪ S.Con] : S.Consistent V := by
  have h : V↓[ℒₒᵣ] ⊧ (S.consistent : ArithmeticSentence) :=
    Semantics.ModelsSet.models_set (T := T ∪ S.Con) (Or.inr rfl)
  simpa [models_iff] using h

end models

/-- The translation of `L` into arithmetic by the Henkin set of `S`. -/
noncomputable def henkinTranslation : DirectTranslation (T ∪ S.Con) L where
  domain := henkinDomain S
  rel := henkinRel S
  func := henkinFunc S
  domain_nonempty := sorry
  func_defined := sorry
  preserve_eq := sorry

end FFL.FirstOrder.Arithmetic
