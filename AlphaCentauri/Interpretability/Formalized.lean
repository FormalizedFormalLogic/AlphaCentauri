module

public import AlphaCentauri.Bootstrapping.Interpretability.Interpretable
public import AlphaCentauri.Bootstrapping.Proof.CutFree
public import AlphaCentauri.ToFoundation.SententialAxioms
public import Foundation.FirstOrder.Incompleteness.StandardProvability

/-!
# Formalized relative interpretability

For an arithmetical theory $T$ with $\Delta_1$ axioms and sentences $\varphi, \psi$, the sentence
`T.interpretability φ ψ` says that $T + \psi$ is interpretable in $T + \varphi$. The theory
$\mathsf{I}\Sigma_1$ proves the arithmetical forms of the principles $\mathbf{J1}$–$\mathbf{J4}$ of
interpretability logic for it.

## References

- [Vis90, §5.5, §6.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The sentence saying that $T + \psi$ is interpretable in $T + \varphi$.
- [Vis90, §5.5] -/
noncomputable def _root_.FFL.FirstOrder.ArithmeticTheory.interpretability
    (φ ψ : ArithmeticSentence) : ArithmeticSentence :=
  interpretableDef ℒₒᵣ ℒₒᵣ (T ∪ {φ}) (T ∪ {ψ})

variable {T}

instance [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence) : 𝗘𝗤 ℒₒᵣ ⪯ T ∪ {φ} :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ T) (inferInstance : T ⪯ T ∪ {φ})

section model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma models_interpretability_iff {φ ψ : ArithmeticSentence} :
    V↓[ℒₒᵣ] ⊧ T.interpretability φ ψ ↔ Interpretable V (T ∪ {φ}) (T ∪ {ψ}) := by
  have : Nonempty V := ⟨0⟩
  exact models_interpretableDef_iff

lemma models_standardProvability_iff_provable {σ : ArithmeticSentence} :
    V↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ Provable T (⌜σ⌝ : V) := by
  simp [Arithmetic.standardProvability_def, models_iff]

lemma consistent_union_singleton_iff {φ : ArithmeticSentence} :
    (T ∪ {φ}).Consistent V ↔ ¬Provable T (⌜∼φ⌝ : V) := by
  have h : Provable T (imp ℒₒᵣ (⌜φ⌝ : V) ⌜(⊥ : ArithmeticSentence)⌝) ↔ Provable T (⌜∼φ⌝ : V) := by
    have e₁ : imp ℒₒᵣ (⌜φ⌝ : V) ⌜(⊥ : ArithmeticSentence)⌝ =
        ((⌜φ⌝ : Bootstrapping.Formula V ℒₒᵣ) 🡒 ⊥).val := by
      simp [Sentence.typed_quote_def, Sentence.quote_def]
      rfl
    have e₂ : (⌜∼φ⌝ : V) = (∼(⌜φ⌝ : Bootstrapping.Formula V ℒₒᵣ)).val := by
      simp [Sentence.typed_quote_def, Sentence.quote_def]
      rfl
    rw [e₁, e₂, ← tprovable_iff_provable, ← tprovable_iff_provable]
    constructor
    · intro h
      cl_prover [h]
    · intro h
      cl_prover [h]
  rw [Theory.Consistent, Derivation.provable_union_singleton_iff, h]

lemma union_singleton_shift_eq [Theory.Δ₁.Sentential T] {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (φ : ArithmeticSentence) :
    ∀ p ∈ (T ∪ {φ}).Δ₁Class (V := V), Bootstrapping.shift ℒₒᵣ p = p :=
  Theory.Δ₁.Sentential.forall_shift_eq (T ∪ {φ})

end model

/-- The arithmetical form of $\mathbf{J4}$: interpretability transfers consistency.
- [Vis90, §6.1] -/
theorem _root_.FFL.FirstOrder.ArithmeticTheory.consistent_of_interpretability
    [𝗘𝗤 ℒₒᵣ ⪯ T] [Theory.Δ₁.Sentential T] {φ ψ : ArithmeticSentence} :
    𝗜𝚺₁ ⊢ T.interpretability φ ψ 🡒 ∼T.standardProvability (∼φ) 🡒
      ∼T.standardProvability (∼ψ) := by
  apply Arithmetic.complete.{0}
  intro V _ _
  simp only [models_iff, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.arrow_eq, LogicalConnective.Prop.neg_eq]
  intro hI hφ
  have hI := models_interpretability_iff.mp hI
  have hφ := consistent_union_singleton_iff.mpr (models_standardProvability_iff_provable.not.mp hφ)
  exact models_standardProvability_iff_provable.not.mpr <| consistent_union_singleton_iff.mp <|
    hI.consistent (union_singleton_shift_eq φ) Language.SymbolsStandard.oRing hφ

end FFL.FirstOrder.Arithmetic
