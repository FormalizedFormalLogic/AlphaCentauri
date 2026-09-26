module

public import AlphaCentauri.Reflection.Unboundedness
public import AlphaCentauri.ToFoundation.Coding
public import AlphaCentauri.ToFoundation.Semiformula
public import AlphaCentauri.ToFoundation.SubstNumeral

@[expose] public section
/-!
# Local $\Sigma_1$ reflection as the numeral instances of one formula

`sigma1ReflectionFormula T` is
$\theta(x) :\equiv (\mathrm{Sent}(x) \wedge \mathrm{Str}\Sigma_1(x) \wedge \mathrm{Pr}_T(x)) \to
\mathrm{Tr}_{\Sigma_1}(x)$, built from the recognizer of strict $\Sigma_1$ codes and the strict
$\Sigma_1$ partial truth predicate. Its numeral instances axiomatize local $\Sigma_1$ reflection
over `T`. A strict $\Pi_2$ prenex form of it gives a $\Delta_1$-presented set of strict $\Pi_2$
sentences, `sigma1ReflectionTheory T`, with the same property.

- [AB05, §4.2]
-/

namespace FFL.FirstOrder.Arithmetic

open FFL.Entailment Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The $\Sigma_1$ formula saying that `x` codes a strict $\Sigma_1$ sentence provable in `T`; a
code without free variables is one fixed by `shift`. -/
noncomputable def sigma1ReflectionPremise : 𝚺₁.Semisentence 1 := .mkSigma
  “x. !(isSemiformula ℒₒᵣ).sigma 0 x ∧ !(shiftGraph ℒₒᵣ) x x ∧ !(isStrictSigma 1).sigma x ∧
    !(provable T) x”

/-- The $\Sigma_1$ formula saying that `x` codes a true strict $\Sigma_1$ formula. -/
noncomputable def sigma1ReflectionConclusion : 𝚺₁.Semisentence 1 := .mkSigma
  “x. !(sigmaSatisfaction 0) x 0”

/-- $\theta(x) :\equiv (\mathrm{Sent}(x) \wedge \mathrm{Str}\Sigma_1(x) \wedge \mathrm{Pr}_T(x))
\to \mathrm{Tr}_{\Sigma_1}(x)$.
- [AB05, §4.2] -/
noncomputable def sigma1ReflectionFormula : ArithmeticSemisentence 1 :=
  (sigma1ReflectionPremise T).val 🡒 sigma1ReflectionConclusion.val

variable {T}

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma eval_sigma1ReflectionPremise (x : V) :
    V ⊧/![x] (sigma1ReflectionPremise T).val ↔
      IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧ IsStrictSigma 1 x ∧ Provable T x := by
  simp [sigma1ReflectionPremise, eq_comm]

lemma eval_sigma1ReflectionConclusion (x : V) :
    V ⊧/![x] sigma1ReflectionConclusion.val ↔ SigmaSatisfaction 1 x 0 := by
  simp [sigma1ReflectionConclusion]

lemma eval_sigma1ReflectionFormula (x : V) :
    V ⊧/![x] (sigma1ReflectionFormula T) ↔
      (IsSemiformula ℒₒᵣ (0 : V) x ∧ shift ℒₒᵣ x = x ∧ IsStrictSigma 1 x ∧ Provable T x →
        SigmaSatisfaction 1 x 0) := by
  simp [sigma1ReflectionFormula, eval_sigma1ReflectionPremise, eval_sigma1ReflectionConclusion]

/-- A standard number that a model of `𝗜𝚺₁` recognizes as the code of a strict $\Sigma_1$
sentence is the code of one. -/
lemma exists_strictSigma1_eq_quote {m : ℕ} (hsemi : IsSemiformula ℒₒᵣ (0 : V) (m : V))
    (hshift : shift ℒₒᵣ (m : V) = m) (hstr : IsStrictSigma 1 (m : V)) :
    ∃ σ : ArithmeticSentence, StrictHierarchy 𝚺 1 σ ∧ m = ⌜σ⌝ := by
  obtain ⟨F, hF⟩ := IsSemiformula.sound (L := ℒₒᵣ) (isSemiformula_natCast_iff (V := V) |>.mpr hsemi)
  have hshiftN : shift ℒₒᵣ m = m := by
    have h := DefinedFunction.shigmaOne_absolute_func V
      (shift.defined (L := ℒₒᵣ) (V := ℕ)) (shift.defined (L := ℒₒᵣ) (V := V)) ![m]
    simp only [Matrix.cons_val_zero, Function.comp_apply] at h
    exact_mod_cast h.trans hshift
  have hF' : Rewriting.shift F = F := by
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp
    rw [Semiformula.quote_shift, hF, hshiftN]
  let σ : ArithmeticSentence := F.toEmpty (Semiformula.freeVariables_eq_empty_of_shift_eq hF')
  have hσ : (⌜σ⌝ : ℕ) = m := by simp [σ, Sentence.quote_def, hF]
  refine ⟨σ, ?_, hσ.symm⟩
  rw [← isStrictSigma_quote_iff (V := V), ← Sentence.coe_quote_eq_quote, hσ]
  exact hstr

end

/-- `𝗜𝚺₁` proves the instance of `sigma1ReflectionFormula T` at a number that codes no strict
$\Sigma_1$ sentence.
- [AB05, §4.2] -/
theorem provable_sigma1ReflectionFormula_of_not_code {n : ℕ}
    (h : ∀ σ : ArithmeticSentence, StrictHierarchy 𝚺 1 σ → n ≠ ⌜σ⌝) :
    𝗜𝚺₁ ⊢ (sigma1ReflectionFormula T)/[↑n] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have hV : V ⊧/![(n : V)] (sigma1ReflectionFormula T) := by
      rw [eval_sigma1ReflectionFormula]
      rintro ⟨hsemi, hshift, hstr, -⟩
      obtain ⟨σ, hσ, rfl⟩ := exists_strictSigma1_eq_quote hsemi hshift hstr
      exact absurd rfl (h σ hσ)
    simpa [models_iff, numeral_eq_natCast] using hV

/-- At the code of a strict $\Sigma_1$ sentence `σ`, `sigma1ReflectionFormula T` is `𝗜𝚺₁`-provably
the reflection instance for `σ`.
- [AB05, §4.2] -/
theorem provable_sigma1ReflectionFormula_iff {σ : ArithmeticSentence}
    (hσ : StrictHierarchy 𝚺 1 σ) :
    𝗜𝚺₁ ⊢ (sigma1ReflectionFormula T)/[↑(⌜σ⌝ : ℕ)] 🡘 (T.standardProvability σ 🡒 σ) :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    have ht : SigmaSatisfaction 1 (⌜σ⌝ : V) 0 ↔ V↓[ℒₒᵣ] ⊧ σ := by
      simpa [models_iff] using sigmaSatisfaction_quote_iff hσ (![] : Fin 0 → V)
    have h : V ⊧/![(⌜σ⌝ : V)] (sigma1ReflectionFormula T) ↔
        (Provable T (⌜σ⌝ : V) → V↓[ℒₒᵣ] ⊧ σ) := by
      rw [eval_sigma1ReflectionFormula, ← ht]
      simp [(isStrictSigma_quote_iff σ).mpr hσ]
    simpa [models_iff, Arithmetic.standardProvability_def, numeral_eq_natCast] using h

variable (T) in
lemma exists_matrix_sigma1ReflectionPremise :
    ∃ θ : 𝚺₀.Semisentence 2, 𝗜𝚺₁ ⊢ ∀¹* ((sigma1ReflectionPremise T).val 🡘 ∃¹ θ.val) :=
  ISigma1.exists_matrix_provable (by simp)

lemma exists_matrix_sigma1ReflectionConclusion :
    ∃ θ : 𝚺₀.Semisentence 2, 𝗜𝚺₁ ⊢ ∀¹* (sigma1ReflectionConclusion.val 🡘 ∃¹ θ.val) :=
  ISigma1.exists_matrix_provable (by simp)

variable (T) in
/-- A $\Delta_0$ matrix of a prenex form of `sigma1ReflectionPremise T`. -/
noncomputable def sigma1ReflectionPremiseMatrix : 𝚺₀.Semisentence 2 :=
  (exists_matrix_sigma1ReflectionPremise T).choose

/-- A $\Delta_0$ matrix of a prenex form of `sigma1ReflectionConclusion`. -/
noncomputable def sigma1ReflectionConclusionMatrix : 𝚺₀.Semisentence 2 :=
  exists_matrix_sigma1ReflectionConclusion.choose

variable (T) in
/-- A strict $\Pi_2$ formula equivalent to `sigma1ReflectionFormula T` over `𝗜𝚺₁`. The vacuous
disjunct `x ≠ x` makes the free variable occur in every numeral instance. -/
noncomputable def sigma1ReflectionFormulaStrict : ArithmeticSemisentence 1 :=
  “x. ∀ u, ∃ w, x ≠ x ∨ ¬!(sigma1ReflectionPremiseMatrix T).val u x ∨
    !sigma1ReflectionConclusionMatrix.val w x”

lemma strictHierarchy_sigma1ReflectionFormulaStrict :
    StrictHierarchy 𝚷 2 (sigma1ReflectionFormulaStrict T) := by
  apply StrictHierarchy.all
  apply StrictHierarchy.ofAlt
  apply StrictHierarchy.exs
  apply StrictHierarchy.of_deltaZero
  simp

lemma le_quote_sigma1ReflectionFormulaStrict (n : ℕ) :
    n ≤ (⌜((sigma1ReflectionFormulaStrict T)/[↑n] : ArithmeticSentence)⌝ : ℕ) := by
  simp only [sigma1ReflectionFormulaStrict, Rewriting.app_all, Rewriting.app_exs,
    LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg, Rew.hom_finitary2,
    Sentence.quote_def, Rew.q_emb, Semiformula.quote_all, Semiformula.quote_ex,
    Semiformula.quote_or]
  apply LE.le.trans' <| le_of_lt <|
    lt_trans (lt_or_left _ _) (lt_trans (lt_exists _) (lt_forall _))
  have : (2 : Fin 3) = (0 : Fin 1).succ.succ := rfl
  rw [this, Rew.q_bvar_succ, Rew.q_bvar_succ]
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

lemma eval_sigma1ReflectionFormulaStrict (x : V) :
    V ⊧/![x] (sigma1ReflectionFormulaStrict T) ↔ V ⊧/![x] (sigma1ReflectionFormula T) := by
  have hA := models_of_provable (M := V) inferInstance
    (exists_matrix_sigma1ReflectionPremise T).choose_spec
  have hB := models_of_provable (M := V) inferInstance
    exists_matrix_sigma1ReflectionConclusion.choose_spec
  simp [models_iff] at hA hB
  simp [sigma1ReflectionFormulaStrict, sigma1ReflectionFormula, hA, hB,
    sigma1ReflectionPremiseMatrix, sigma1ReflectionConclusionMatrix, exists_or, imp_iff_not_or,
    forall_or_right]

end

lemma provable_sigma1ReflectionFormulaStrict_iff (n : ℕ) :
    𝗜𝚺₁ ⊢ (sigma1ReflectionFormulaStrict T)/[↑n] 🡘 (sigma1ReflectionFormula T)/[↑n] :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, numeral_eq_natCast] using eval_sigma1ReflectionFormulaStrict (T := T) (n : V)

variable (T) in
/-- The numeral instances of `sigma1ReflectionFormulaStrict T`. -/
noncomputable def sigma1ReflectionTheory : ArithmeticTheory :=
  Set.range fun n : ℕ ↦ ((sigma1ReflectionFormulaStrict T)/[↑n] : ArithmeticSentence)

noncomputable instance : (sigma1ReflectionTheory T).Δ₁ :=
  Theory.Δ₁.numeralInstances _ le_quote_sigma1ReflectionFormulaStrict

variable [𝗜𝚺₁ ⪯ T]

/-- Local $\Sigma_1$ reflection over `T` is axiomatized by the numeral instances of
`sigma1ReflectionFormula T`.
- [AB05, §4.2] -/
theorem localReflectionOn_Sigma1_equiv_union_range :
    T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T ≊
      T ∪ Set.range fun n : ℕ ↦ ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence) := by
  set R := Set.range fun n : ℕ ↦ ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence)
  have hR : 𝗜𝚺₁ ⪯ T ∪ R :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left)
  have hRfn : 𝗜𝚺₁ ⪯ T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left)
  have hstrict : T ∪ R ⊢* 𝗥𝗳𝗻[StrictHierarchy 𝚺 1] T := by
    rintro _ ⟨σ, hσ, rfl⟩
    have h₁ : T ∪ R ⊢ (sigma1ReflectionFormula T)/[↑(⌜σ⌝ : ℕ)] :=
      by_axm <| Set.mem_union_right _ ⟨⌜σ⌝, rfl⟩
    have h₂ := hR.pbl (provable_sigma1ReflectionFormula_iff (T := T) hσ)
    cl_prover [h₁, h₂]
  have hbroad : T ∪ R ⊢* 𝗥𝗳𝗻[Hierarchy 𝚺 1] T :=
    provable_localReflectionOn_hierarchy_of_strictHierarchy (n := 1)
    (WeakerThan.ofSubset Set.subset_union_left) hstrict
  apply Equiv.antisymm
  constructor
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | hφ)
    · exact by_axm <| Set.mem_union_left _ hφ
    · exact hbroad hφ
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | ⟨n, rfl⟩)
    · exact by_axm <| Set.mem_union_left _ hφ
    · by_cases hn : ∃ σ : ArithmeticSentence, StrictHierarchy 𝚺 1 σ ∧ n = ⌜σ⌝
      · obtain ⟨σ, hσ, rfl⟩ := hn
        have h₁ : T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T ⊢ T.standardProvability σ 🡒 σ :=
          by_axm <| Set.mem_union_right _ ⟨σ, hσ.hierarchy, rfl⟩
        have h₂ := hRfn.pbl (provable_sigma1ReflectionFormula_iff (T := T) hσ)
        cl_prover [h₁, h₂]
      · exact hRfn.pbl <|
          provable_sigma1ReflectionFormula_of_not_code fun σ hσ e ↦ hn ⟨σ, hσ, e⟩

/-- Local $\Sigma_1$ reflection over `T` is axiomatized by `sigma1ReflectionTheory T`.
- [AB05, §4.2] -/
theorem localReflectionOn_Sigma1_equiv_union_sigma1ReflectionTheory :
    T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T ≊ T ∪ sigma1ReflectionTheory T := by
  apply localReflectionOn_Sigma1_equiv_union_range.trans
  have hR : 𝗜𝚺₁ ⪯ T ∪ Set.range fun n : ℕ ↦
      ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence) :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left)
  have hS : 𝗜𝚺₁ ⪯ T ∪ sigma1ReflectionTheory T :=
    WeakerThan.trans (𝓣 := T) inferInstance (WeakerThan.ofSubset Set.subset_union_left)
  apply Equiv.antisymm
  constructor
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | ⟨n, rfl⟩)
    · exact by_axm <| Set.mem_union_left _ hφ
    · have h₁ : T ∪ sigma1ReflectionTheory T ⊢ (sigma1ReflectionFormulaStrict T)/[↑n] :=
        by_axm <| Set.mem_union_right _ ⟨n, rfl⟩
      have h₂ := hS.pbl (provable_sigma1ReflectionFormulaStrict_iff (T := T) n)
      cl_prover [h₁, h₂]
  · apply WeakerThan.ofAxm!
    rintro φ (hφ | ⟨n, rfl⟩)
    · exact by_axm <| Set.mem_union_left _ hφ
    · have h₁ : T ∪ (Set.range fun n : ℕ ↦ ((sigma1ReflectionFormula T)/[↑n] : ArithmeticSentence))
          ⊢ (sigma1ReflectionFormula T)/[↑n] :=
        by_axm <| Set.mem_union_right _ ⟨n, rfl⟩
      have h₂ := hR.pbl (provable_sigma1ReflectionFormulaStrict_iff (T := T) n)
      cl_prover [h₁, h₂]

/-- Local $\Sigma_1$ reflection over `T` is axiomatized over `T` by a $\Delta_1$-presented set of
strict $\Pi_2$ sentences.
- [AB05, §4.2] -/
theorem exists_strictPi2_axiomatization_localReflectionOn_Sigma1 :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁), (∀ σ ∈ U, StrictHierarchy 𝚷 2 σ) ∧
      T ∪ 𝗥𝗳𝗻[Hierarchy 𝚺 1] T ≊ T ∪ U := by
  have h : ∀ σ ∈ sigma1ReflectionTheory T, StrictHierarchy 𝚷 2 σ := by
    rintro _ ⟨n, rfl⟩
    exact StrictHierarchy.rew _ strictHierarchy_sigma1ReflectionFormulaStrict
  exact ⟨_, inferInstance, h, localReflectionOn_Sigma1_equiv_union_sigma1ReflectionTheory⟩

end FFL.FirstOrder.Arithmetic
