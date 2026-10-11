module

public import AlphaCentauri.Interpretability.HenkinTruth

/-!
# Interpretation of a theory in itself plus its consistency

A theory $S$ with a $\Delta_1$ numeration and the equality axioms is interpretable in
$T + \mathrm{Con}_S$ for every arithmetical theory $T \supseteq \mathsf{PA}$.

## References

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.27], [HP98, 2.43]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Eq] (S : Theory L) [S.Δ₁]
  [𝗘𝗤 L ⪯ S] (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section sentential

variable [Theory.Δ₁.Sentential S]

/-- The Henkin translation interprets `S` in `T ∪ S.Con` when the numeration of `S` consists of
sentences. -/
noncomputable abbrev henkinInterpretationOfSentential : T ∪ S.Con ⊳ S where
  trln := henkinTranslation S T
  interpret_theory σ hσ := Arithmetic.complete.{0} _ _ fun V _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (T := 𝗣𝗔) (U := T ∪ S.Con) inferInstance
    have hcons := consistent_of_models_con S T (V := V)
    have hS : ∀ p ∈ S.Δ₁Class (V := V), shift L p = p := fun _ h ↦ Theory.Δ₁.Sentential.shift_eq h
    have : Nonempty V := ⟨0⟩
    rw [DirectTranslation.Model.translate_iff]
    simp only [models_iff]
    have h := henkinTranslation_truth S T (V := V) σ (e := ![]) (u := ![]) (fun i ↦ i.elim0)
    refine h.mpr ?_
    rw [Bootstrapping.Semiformula.subst_nil_eq_self]
    exact HenkinSet.of_provable S (by simp) (internalize_provability (Entailment.by_axm hσ))

end sentential

omit [𝗘𝗤 L ⪯ S] [L.Eq] in
/-- The consistency statement of `S` for the numeration restricted to sentences follows from its
consistency statement for the given numeration. -/
lemma weakerThan_con_sentential :
    T ∪ @Theory.Con L _ _ S (Theory.Δ₁.sentential S inferInstance) ⪯ T ∪ S.Con :=
  Arithmetic.weakerThan_of_models.{0} _ _ fun (V : Type) _ _ ↦ by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (T := 𝗣𝗔) (U := T ∪ S.Con) inferInstance
    have h₀ := Theory.Δ₁.sentential_consistent S (consistent_of_models_con S T (V := V))
    have hT : V↓[ℒₒᵣ] ⊧* T := models_of_ss (U := T ∪ S.Con) inferInstance Set.subset_union_left
    refine ⟨fun σ hσ ↦ ?_⟩
    rcases hσ with hσ | rfl
    · exact Semantics.ModelsSet.models_set hσ
    · simpa [models_iff] using h₀

/-- The theory `S` is interpretable in `T` and the consistency of `S`.

- [Lin97, Theorem 6.4]
- [HP98, Theorem I.4.27], [HP98, 2.43] -/
noncomputable abbrev henkinInterpretation : T ∪ S.Con ⊳ S :=
  haveI := weakerThan_con_sentential S T
  (@henkinInterpretationOfSentential L _ _ _ S (Theory.Δ₁.sentential S inferInstance) _ T _ _
    ).ofWeakerThanLeft

end FFL.FirstOrder.Arithmetic
