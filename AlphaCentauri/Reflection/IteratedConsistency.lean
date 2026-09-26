module

public import AlphaCentauri.ToFoundation.ProvabilityLogic.AddTBB
public import AlphaCentauri.ToFoundation.SubstNumeral
public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex

@[expose] public section
/-!
# A strict $\Pi_1$ axiomatization of $T_\omega$

`T.addTBB T Set.univ` is $T_\omega = T + \{\neg\Box_T^{n + 1}\bot\}_n$. It is equivalent to `T`
extended by the $\Delta_1$-presented set `notProvableIterateBotTheory T` of strict $\Pi_1$
sentences: the numeral instances of one strict $\Pi_1$ formula, which `𝗜𝚺₁` proves equivalent to
$\neg\mathrm{Pr}_T(\ulcorner\Box_T^{x}\bot\urcorner)$.

- [AB05, §4.1]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping ArithmeticTheory

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The $\Pi_1$ formula $\neg\mathrm{Pr}_T(\ulcorner\Box_T^{x}\bot\urcorner)$, with the code of
$\Box_T^{x}\bot$ computed by `substNumeralItr`. -/
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
/-- A $\Delta_0$ matrix of a prenex form of `notProvableIterateBot T`. -/
noncomputable def notProvableIterateBotMatrix : 𝚺₀.Semisentence 2 :=
  (exists_matrix_notProvableIterateBot T).choose

variable (T) in
/-- A strict $\Pi_1$ formula equivalent to `notProvableIterateBot T` over `𝗜𝚺₁`. The vacuous
disjunct `x ≠ x` makes the free variable occur in every numeral instance. -/
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
  apply LE.le.trans' (le_of_lt <| lt_trans (lt_or_left _ _) (lt_forall _))
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
/-- The numeral instances of `notProvableIterateBotStrict T`. -/
noncomputable def notProvableIterateBotTheory : ArithmeticTheory :=
  Set.range fun n : ℕ ↦ ((notProvableIterateBotStrict T)/[↑n] : ArithmeticSentence)

noncomputable instance : (notProvableIterateBotTheory T).Δ₁ :=
  Theory.Δ₁.numeralInstances _ le_quote_notProvableIterateBotStrict

variable [𝗜𝚺₁ ⪯ T]

/-- $T_\omega$ is equivalent to `T` extended by `notProvableIterateBotTheory T`.
- [AB05, §4.1] -/
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
      simp only [ProvabilityLogic.Formula.interpret_TBB]
      cl_prover [h₁, h₂]
  · apply WeakerThan.ofAxm!
    rintro σ (hσ | ⟨n, rfl⟩)
    · exact by_axm <| Set.mem_union_left _ hσ
    · have h₁ : T.addTBB T Set.univ ⊢ ∼(T.standardProvability^[n + 1] ⊥) :=
        provable_neg_iterate_addTBB fun i _ ↦ Set.mem_univ i
      have h₂ := (inferInstance : 𝗜𝚺₁ ⪯ T.addTBB T Set.univ).pbl
        (provable_notProvableIterateBotStrict_iff (T := T) n)
      cl_prover [h₁, h₂]

/-- $T_\omega$ is `T` extended by a $\Delta_1$-presented set of strict $\Pi_1$ sentences.
- [AB05, §4.1] -/
theorem exists_strictPi1_axiomatization_addTBB :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, StrictHierarchy 𝚷 1 σ) ∧
      T.addTBB T Set.univ ≊ T ∪ U := by
  have h : ∀ σ ∈ notProvableIterateBotTheory T, StrictHierarchy 𝚷 1 σ := by
    rintro _ ⟨n, rfl⟩
    exact StrictHierarchy.rew _ strictHierarchy_notProvableIterateBotStrict
  exact ⟨_, inferInstance, h, addTBB_equiv_union_notProvableIterateBotTheory⟩

end FFL.FirstOrder.Arithmetic
