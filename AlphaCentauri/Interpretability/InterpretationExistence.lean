module

public import AlphaCentauri.Interpretability.Formalized
public import AlphaCentauri.Interpretability.Henkin

/-!
# The formalized interpretation existence lemma

For an arithmetical theory $T \supseteq \mathsf{PA}$ with $\Delta_1$ axioms and a sentence
$\varphi$, $\mathsf{I}\Sigma_1$ proves that $T + \neg\mathrm{Pr}_T(\neg\varphi)$ interprets
$T + \varphi$: the Henkin translation of $T + \varphi$ interprets it. This is the arithmetical form
of the principle $\mathbf{J5}$ of interpretability logic.

## References

- [Vis90, §6.2.2.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

section henkin

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [Theory.Δ₁.Sentential S] [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔 ⪯ T]

/-- In every model of $\mathsf{I}\Sigma_1$, along a table of the Henkin translation of `S`, every
axiom of `S` translates to a formula provable from `T` and the consistency of `S`.
- [Vis90, §6.2.2.1] -/
axiom provable_translate_henkinTranslation {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {tbl : V} (h : IsTableOf (henkinTranslation S T) tbl) {p : V} (hp : p ∈ S.Δ₁Class)
    (hf : IsFormula L p) : Provable (T ∪ S.Con) (translate ℒₒᵣ L tbl p)

end henkin

section existence

variable {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔 ⪯ T] [Theory.Δ₁.Sentential T] (φ : ArithmeticSentence)

omit [Theory.Δ₁.Sentential T] in
/-- The consistency of $T + \varphi$ follows from $T + \neg\mathrm{Pr}_T(\neg\varphi)$. -/
lemma weakerThan_union_con_union_singleton :
    T ∪ (T ∪ {φ}).Con ⪯ T ∪ {∼T.standardProvability (∼φ)} :=
  Arithmetic.weakerThan_of_models.{0} _ _ fun (V : Type) _ _ ↦ by
    have : 𝗜𝚺₁ ⪯ T ∪ {∼T.standardProvability (∼φ)} :=
      Entailment.WeakerThan.trans (Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ 𝗣𝗔)
        (inferInstance : 𝗣𝗔 ⪯ T)) inferInstance
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
      models_of_subtheory (T := 𝗜𝚺₁) (U := T ∪ {∼T.standardProvability (∼φ)}) inferInstance
    have hσ : V↓[ℒₒᵣ] ⊧ ∼T.standardProvability (∼φ) :=
      Semantics.ModelsSet.models_set (T := T ∪ {∼T.standardProvability (∼φ)}) (Or.inr rfl)
    have hcon : (T ∪ {φ}).Consistent V := consistent_union_singleton_iff.mpr <|
      models_standardProvability_iff_provable.not.mp (by simpa [models_iff] using hσ)
    refine ⟨fun χ hχ ↦ ?_⟩
    rcases hχ with hχ | rfl
    · exact Semantics.ModelsSet.models_set (T := T ∪ {∼T.standardProvability (∼φ)}) (Or.inl hχ)
    · simpa [models_iff] using hcon

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

omit [𝗣𝗔 ⪯ T] [Theory.Δ₁.Sentential T] in
lemma provable_union_singleton_of_provable_union_singleton {σ χ : ArithmeticSentence}
    (hχ : T ∪ {σ} ⊢ χ) {x : V} (h : Provable (T ∪ {χ}) x) : Provable (T ∪ {σ}) x := by
  rw [Derivation.provable_union_singleton_iff] at h
  have h₁ : Provable (T ∪ {σ}) (imp ℒₒᵣ ⌜χ⌝ x) :=
    (h.toDerivable.of_ss fun _ hp ↦ Theory.Δ₁Class.mem_union.mpr (Or.inl hp)).toProvable
  exact provable_of_provable_imp_of_provable h₁ (internalize_provability hχ)

/-- In every model of $\mathsf{I}\Sigma_1$, $T + \varphi$ is interpretable in
$T + \neg\mathrm{Pr}_T(\neg\varphi)$.
- [Vis90, §6.2.2.1] -/
theorem interpretable_union_singleton_neg_standardProvability_neg :
    Interpretable V (T ∪ {∼T.standardProvability (∼φ)}) (T ∪ {φ}) := by
  have := weakerThan_union_con_union_singleton (T := T) φ
  let π : DirectTranslation (T ∪ {∼T.standardProvability (∼φ)}) ℒₒᵣ :=
    (henkinTranslation (L := ℒₒᵣ) (T ∪ ({φ} : ArithmeticTheory)) T).ofWeakerThan
  have hπ : IsTableOf π (arithmeticTable (V := V) π) := isTableOf_arithmeticTable π
  use arithmeticTable π
  refine { toIsTranslationTable := hπ.isTranslationTable Language.SymbolsStandard.oRing,
           translate_axiom := fun {p} hp hf ↦ ?_ }
  have hχ : T ∪ {∼T.standardProvability (∼φ)} ⊢ (T ∪ {φ}).consistent.val :=
    Entailment.WeakerThan.pbl (𝓢 := T ∪ (T ∪ {φ}).Con) (Entailment.by_axm (Or.inr rfl))
  exact provable_union_singleton_of_provable_union_singleton hχ <|
    provable_translate_henkinTranslation (T ∪ {φ}) T hπ.of_ofWeakerThan hp hf

/-- The arithmetical form of $\mathbf{J5}$, the formalized interpretation existence lemma:
$T + \neg\mathrm{Pr}_T(\neg\varphi)$ interprets $T + \varphi$.
- [Vis90, §6.2.2.1] -/
theorem _root_.FFL.FirstOrder.ArithmeticTheory.interpretability_consistency :
    𝗜𝚺₁ ⊢ T.interpretability (∼T.standardProvability (∼φ)) φ :=
  Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    models_interpretability_iff.mpr (interpretable_union_singleton_neg_standardProvability_neg φ)

end existence

end FFL.FirstOrder.Arithmetic
