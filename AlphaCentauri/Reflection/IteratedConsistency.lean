module

public import AlphaCentauri.ToFoundation.SubstNumeral
public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex
public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.Meta.ClProver

@[expose] public section
/-!
# A strict $\Pi_1$ axiomatization of $T_\omega$
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

noncomputable def notProvableIterateBot : 𝚷₁.Semisentence 1 := .mkPi
  “x. ∀ y, !substNumeralItrDef y !!(⌜(provable T).val⌝) !!(⌜(⊥ : ArithmeticSentence)⌝) x →
    ¬!(provable T) y”

variable {T}

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma eval_notProvableIterateBot (x : V) :
    V ⊧/![x] (notProvableIterateBot T).val ↔
      ¬Provable T (substNumeralItr ⌜(provable T).val⌝ ⌜(⊥ : ArithmeticSentence)⌝ x) := by
  simp [notProvableIterateBot]

lemma substNumeralItr_provable_bot (n : ℕ) :
    substNumeralItr (⌜(provable T).val⌝ : V) ⌜(⊥ : ArithmeticSentence)⌝ (n : V) =
      ⌜T.standardProvability^[n] ⊥⌝ :=
  substNumeralItr_quote _ _ n

end

variable (T) in
lemma exists_matrix_notProvableIterateBot :
    ∃ θ : 𝚺₀.Semisentence 2, 𝗜𝚺₁ ⊢ ∀¹* ((notProvableIterateBot T).val 🡘 ∀¹ θ.val) :=
  ISigma1.exists_matrix_provable_pi (by simp)

variable (T) in
noncomputable def notProvableIterateBotMatrix : 𝚺₀.Semisentence 2 :=
  (exists_matrix_notProvableIterateBot T).choose

variable (T) in
noncomputable def notProvableIterateBotStrict : ArithmeticSemisentence 1 :=
  “x. ∀ y, x ≠ x ∨ !(notProvableIterateBotMatrix T).val y x”

lemma strictHierarchy_notProvableIterateBotStrict :
    StrictHierarchy 𝚷 1 (notProvableIterateBotStrict T) := by
  apply StrictHierarchy.all
  apply StrictHierarchy.of_deltaZero
  simp

lemma le_quote_notProvableIterateBotStrict (n : ℕ) :
    n ≤ (⌜((notProvableIterateBotStrict T)/[↑n] : ArithmeticSentence)⌝ : ℕ) := by
  simp only [notProvableIterateBotStrict, Rewriting.app_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, Rew.hom_finitary2, Sentence.quote_def, Rew.q_emb,
    Semiformula.quote_all, Semiformula.quote_or]
  refine le_trans ?_ (le_of_lt <| lt_trans (lt_or_left _ _) (lt_forall _))
  have : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  rw [this, Rew.q_bvar_succ]
  simp only [Semiformula.quote_def, Rew.subst_bvar, Matrix.cons_val_fin_one, Rew.finitary0,
    LCWQIsoGödelQuote.neg, Semiformula.typed_quote_eq, Semiterm.typed_quote_numeral_eq_numeral,
    natCast_nat, Arithmetic.neg_equals, Arithmetic.val_notEquals,
    Bootstrapping.Arithmetic.val_numeral]
  have h := Arithmetic.lt_qqNEQ_left (V := ℕ) (Arithmetic.numeral n) (Arithmetic.numeral n)
  rcases Arithmetic.le_numeral_self (V := ℕ) n with e | e
  · exact e ▸ h.le
  · exact (e.trans h).le

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma eval_notProvableIterateBotStrict (x : V) :
    V ⊧/![x] (notProvableIterateBotStrict T) ↔ V ⊧/![x] (notProvableIterateBot T).val := by
  have h := models_of_provable (M := V) inferInstance
    (exists_matrix_notProvableIterateBot T).choose_spec
  simp [models_iff] at h
  simp [notProvableIterateBotStrict, h, notProvableIterateBotMatrix]

end

lemma provable_notProvableIterateBotStrict_iff (n : ℕ) :
    𝗜𝚺₁ ⊢ (notProvableIterateBotStrict T)/[↑n] 🡘 ∼(T.standardProvability^[n + 1] ⊥) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have h : V ⊧/![(n : V)] (notProvableIterateBotStrict T) ↔
        ¬Provable T (⌜T.standardProvability^[n] ⊥⌝ : V) := by
      rw [eval_notProvableIterateBotStrict, eval_notProvableIterateBot,
        substNumeralItr_provable_bot]
    simpa [models_iff, Function.iterate_succ_apply', Arithmetic.standardProvability_def,
      numeral_eq_natCast] using h

variable (T) in
noncomputable def notProvableIterateBotTheory : ArithmeticTheory :=
  Set.range fun n : ℕ ↦ ((notProvableIterateBotStrict T)/[↑n] : ArithmeticSentence)

noncomputable instance : (notProvableIterateBotTheory T).Δ₁ :=
  Theory.Δ₁.numeralInstances _ le_quote_notProvableIterateBotStrict

open ProvabilityLogic Formula in
lemma interpret_TBB (n : ℕ) :
    (TBB n : LetterlessFormula).interpret ⟨Empty.elim⟩ T.standardProvability =
      (T.standardProvability^[n + 1] ⊥ 🡒 T.standardProvability^[n] ⊥) := by
  simp [TBB, interpret, Function.iterate_succ_apply']

lemma addTBB_provable_neg_iterate (n : ℕ) :
    T.addTBB T Set.univ ⊢ ∼(T.standardProvability^[n] ⊥) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id]; cl_prover
  | succ n ih =>
    have h : T.addTBB T Set.univ ⊢ T.standardProvability^[n + 1] ⊥ 🡒 T.standardProvability^[n] ⊥ :=
      by_axm <| Set.mem_union_right T ⟨n, Set.mem_univ n, interpret_TBB n⟩
    cl_prover [h, ih]

variable [𝗜𝚺₁ ⪯ T]

theorem addTBB_equiv_union_notProvableIterateBotTheory :
    T.addTBB T Set.univ ≊ T ∪ notProvableIterateBotTheory T := by
  have hU : 𝗜𝚺₁ ⪯ T ∪ notProvableIterateBotTheory T :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left)
  apply Equiv.antisymm
  constructor
  · apply WeakerThan.ofAxm!
    rintro σ (hσ | ⟨n, -, rfl⟩)
    · exact by_axm <| Set.mem_union_left _ hσ
    · have h₁ : T ∪ notProvableIterateBotTheory T ⊢ (notProvableIterateBotStrict T)/[↑n] :=
        by_axm <| Set.mem_union_right _ ⟨n, rfl⟩
      have h₂ := hU.pbl (provable_notProvableIterateBotStrict_iff (T := T) n)
      simp only [interpret_TBB]
      cl_prover [h₁, h₂]
  · apply WeakerThan.ofAxm!
    rintro σ (hσ | ⟨n, rfl⟩)
    · exact by_axm <| Set.mem_union_left _ hσ
    · have h₁ := addTBB_provable_neg_iterate (T := T) (n + 1)
      have h₂ := (inferInstance : 𝗜𝚺₁ ⪯ T.addTBB T Set.univ).pbl
        (provable_notProvableIterateBotStrict_iff (T := T) n)
      cl_prover [h₁, h₂]

theorem exists_strictPi1_axiomatization_addTBB :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, StrictHierarchy 𝚷 1 σ) ∧
      T.addTBB T Set.univ ≊ T ∪ U := by
  refine ⟨notProvableIterateBotTheory T, inferInstance, ?_,
    addTBB_equiv_union_notProvableIterateBotTheory⟩
  rintro _ ⟨n, rfl⟩
  exact StrictHierarchy.rew _ strictHierarchy_notProvableIterateBotStrict

end FFL.FirstOrder.Arithmetic
