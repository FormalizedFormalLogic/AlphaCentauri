module

public import AlphaCentauri.Bootstrapping.PartialTruth.Tarski

/-!
# Partial truth definitions agree with truth

This module proves the “it's snowing” agreement between partial satisfaction and semantics,
both in every model of `𝗜𝚺₁` and, uniformly, over `𝗣𝗔⁻` together with the finite Tarski theory.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Codes of quoted semisentences

Foundation's `quote_*` lemmas compute the code of a `Semiproposition`. A `Semisentence` is
quoted through its embedding (`Sentence.quote_def`), so each of them has a counterpart here,
proved by unfolding that embedding. -/

/-- A coded closed term is a well-formed internal term.
- [HP98, 1.66] -/
private lemma isUTerm_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) : IsUTerm ℒₒᵣ (⌜t⌝ : V) := by
  simp [Semiterm.empty_quote_eq]

/-- A coded semisentence is a well-formed internal formula.
- [HP98, 1.66] -/
private lemma isUFormula_quote {k : ℕ} (φ : ArithmeticSemisentence k) :
    IsUFormula ℒₒᵣ (⌜φ⌝ : V) := (Sentence.quote_isSemiformula φ).isUFormula

/-- The code of an equation between closed terms.
- [HP98, 1.66] -/
private lemma quote_eq_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.rel Language.Eq.eq ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqEQ (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_rel, Arithmetic.qqEQ, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_eq (V := V)

/-- The code of a negated equation between closed terms.
- [HP98, 1.66] -/
private lemma quote_neq_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.nrel Language.Eq.eq ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqNEQ (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_nrel, Arithmetic.qqNEQ, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_eq (V := V)

/-- The code of a comparison between closed terms.
- [HP98, 1.66] -/
private lemma quote_lt_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.rel Language.LT.lt ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqLT (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_rel, Arithmetic.qqLT, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_lt (V := V)

/-- The code of a negated comparison between closed terms.
- [HP98, 1.66] -/
private lemma quote_nlt_sentence {k : ℕ} (t u : ClosedSemiterm ℒₒᵣ k) :
    (⌜(.nrel Language.LT.lt ![t, u] : ArithmeticSemisentence k)⌝ : V)
      = Arithmetic.qqNLT (⌜t⌝ : V) (⌜u⌝ : V) := by
  simpa [Sentence.quote_def, Semiformula.quote_nrel, Arithmetic.qqNLT, Semiterm.empty_quote_eq,
    Semiterm.empty_typed_quote_def, Matrix.vecHead, Matrix.vecTail] using coe_quote_lt (V := V)

/-- The code of a conjunction of semisentences.
- [HP98, 1.66] -/
private lemma quote_and_sentence {k : ℕ} (φ ψ : ArithmeticSemisentence k) :
    (⌜φ ⋏ ψ⌝ : V) = (⌜φ⌝ : V) ^⋏ (⌜ψ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of a disjunction of semisentences.
- [HP98, 1.66] -/
private lemma quote_or_sentence {k : ℕ} (φ ψ : ArithmeticSemisentence k) :
    (⌜φ ⋎ ψ⌝ : V) = (⌜φ⌝ : V) ^⋎ (⌜ψ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of a universally quantified semisentence.
- [HP98, 1.66] -/
private lemma quote_all_sentence {k : ℕ} (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∀¹ φ : ArithmeticSemisentence k)⌝ : V) = ^∀ (⌜φ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of an existentially quantified semisentence.
- [HP98, 1.66] -/
private lemma quote_ex_sentence {k : ℕ} (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∃¹ φ : ArithmeticSemisentence k)⌝ : V) = ^∃ (⌜φ⌝ : V) := by simp [Sentence.quote_def]

/-- The code of a bounded universal quantification; the semisentence form of Foundation's
`quote_ball`.
- [HP98, 0.30] -/
private lemma quote_ball_sentence {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k)
    (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence k)⌝ : V)
      = qqBall (termBShift ℒₒᵣ (⌜t⌝ : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.ball_eq, Semiformula.imp_eq]
  simpa [Sentence.quote_def, Semiformula.Operator.lt_def, Semiformula.neg_rel, qqBall,
    Semiformula.quote_nrel, Arithmetic.qqNLT, Semiterm.empty_quote_eq, Matrix.vecHead,
    Matrix.vecTail, ← Rew.emb_bShift_term,
    ← Semiterm.empty_typed_quote_def] using coe_quote_lt (V := V)

/-- The code of a bounded existential quantification; the semisentence form of `quote_bex`.
- [HP98, 0.30] -/
private lemma quote_bex_sentence {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k)
    (φ : ArithmeticSemisentence (k + 1)) :
    (⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence k)⌝ : V)
      = qqBex (termBShift ℒₒᵣ (⌜t⌝ : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.bexs_eq]
  simpa [Sentence.quote_def, Semiformula.Operator.lt_def, qqBex, Semiformula.quote_rel,
    Arithmetic.qqLT, Semiterm.empty_quote_eq, Matrix.vecHead, Matrix.vecTail,
    ← Rew.emb_bShift_term, ← Semiterm.empty_typed_quote_def] using coe_quote_lt (V := V)

/-- The code of a coded bound variable.
- [HP98, 1.66] -/
private lemma quote_bvar_sentence {k : ℕ} (i : Fin k) :
    (⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : V) = qqBvar (i.val : V) := by
  simp [Semiterm.empty_quote_eq]

/-- The code of the zero term.
- [HP98, 1.66] -/
private lemma quote_zeroTerm_sentence {k : ℕ} (w : Fin 0 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : V) = (𝟎 : V) := by
  rw [Arithmetic.coe_zero_eq,
    show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq]
  simp [Semiterm.empty_quote_eq, quote_zeroIndex_eq]

/-- The code of the one term.
- [HP98, 1.66] -/
private lemma quote_oneTerm_sentence {k : ℕ} (w : Fin 0 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : V) = (𝟏 : V) := by
  rw [Arithmetic.coe_one_eq,
    show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq]
  simp [Semiterm.empty_quote_eq, quote_oneIndex_eq]

/-- The code of a sum of closed terms.
- [HP98, 1.66] -/
private lemma quote_addTerm_sentence {k : ℕ} (w : Fin 2 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : V)
      = (⌜w 0⌝ : V) ^+ ⌜w 1⌝ := by
  simp [Semiterm.empty_quote_eq, Arithmetic.qqAdd, quote_addIndex_eq,
    Arithmetic.coe_addIndex_eq, Matrix.vecHead, Matrix.vecTail]

/-- The code of a product of closed terms.
- [HP98, 1.66] -/
private lemma quote_mulTerm_sentence {k : ℕ} (w : Fin 2 → ClosedSemiterm ℒₒᵣ k) :
    (⌜(Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : V)
      = (⌜w 0⌝ : V) ^* ⌜w 1⌝ := by
  simp [Semiterm.empty_quote_eq, Arithmetic.qqMul, quote_mulIndex_eq,
    Arithmetic.coe_mulIndex_eq, Matrix.vecHead, Matrix.vecTail]

/-! ## Agreement of satisfaction with truth -/

/-- For a bounded formula, internal `Δ₀` satisfaction of its code agrees with truth. This is the
base case of the snowing lemma, by recursion on the bounded formula: each clause is the matching
Tarski condition of `SatZero`, and the atoms are `termVal_quote`.
- [HP98, Theorem I.1.70]
- [HP98, Corollary I.1.76] -/
theorem satZero_quote_iff {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : Hierarchy 𝚺 0 φ) (v : Fin k → V) :
    SatZero (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  revert v
  refine delta₀_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ v : Fin k → V, SatZero (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k φ hφ
  · intro n v; simp [Sentence.quote_def]
  · intro n v; simp [Sentence.quote_def]
  · intro n t u v
    rw [quote_eq_sentence, SatZero.eq_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_rel]
  · intro n t u v
    rw [quote_neq_sentence, SatZero.neq_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_nrel]
  · intro n t u v
    rw [quote_lt_sentence, SatZero.lt_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_rel]
  · intro n t u v
    rw [quote_nlt_sentence, SatZero.nlt_iff (isUTerm_quote t) (isUTerm_quote u),
      termVal_quote, termVal_quote]
    simp [Semiformula.eval_nrel]
  · intro n φ ψ hφ hψ ihφ ihψ v
    rw [quote_and_sentence, SatZero.and_iff, ihφ v, ihψ v]
    simp
  · intro n φ ψ hφ hψ ihφ ihψ v
    rw [quote_or_sentence, SatZero.or_iff ((isDelta0_quote_iff φ).mpr hφ) (isUFormula_quote φ)
      ((isDelta0_quote_iff ψ).mpr hψ) (isUFormula_quote ψ), ihφ v, ihψ v]
    simp
  · intro n t φ hφ ihφ v
    rw [quote_ball_sentence, SatZero.ball_iff (isUTerm_quote t)
      ((isDelta0_quote_iff φ).mpr hφ) (isUFormula_quote φ), termVal_quote]
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    refine forall_congr' fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)]
    simp [Function.comp_def]
  · intro n t φ hφ ihφ v
    rw [quote_bex_sentence, SatZero.bex_iff (isUTerm_quote t), termVal_quote]
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    refine exists_congr fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp, ihφ (x :> v)]
    simp [Function.comp_def]

/-- The satisfaction predicate selected by a polarity. It lets one induction on a
`StrictHierarchy` derivation, whose polarity the `zero` and `ofAlt` constructors leave open,
produce the `Σ` and the `Π` statement at once.
- [HP98, Definition I.1.74] -/
def SatClass : Polarity → ℕ → V → V → Prop
  | .sigma, n, z, e => SatSigma n z e
  | .pi, n, z, e => SatPi n z e

/-- Internal satisfaction of the code of a strict prenex formula agrees with truth, by induction
on the derivation of its strict class.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
lemma satClass_quote_iff {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) :
    ∀ v : Fin k → V, SatClass Γ s (⌜φ⌝ : V) (matrixToVec v) ↔ V ⊧/v φ := by
  induction h with
  | @zero Γ₀ n₀ φ₀ hφ₀ =>
    intro v
    rcases Γ₀ with _ | _
    · show SatSigma 0 _ _ ↔ _
      rw [SatSigma.zero]; exact satZero_quote_iff hφ₀ v
    · show SatPi 0 _ _ ↔ _
      rw [SatPi.zero]; exact satZero_quote_iff hφ₀ v
  | @ofAlt Γ₀ s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    rcases Γ₀ with _ | _
    · show SatSigma (s₀ + 1) _ _ ↔ _
      rw [SatSigma.of_pi ((isStrictPi_quote_iff φ₀).mpr hφ₀) (isUFormula_quote φ₀)]
      exact ih v
    · show SatPi (s₀ + 1) _ _ ↔ _
      rw [SatPi.of_sigma ((isStrictSigma_quote_iff φ₀).mpr hφ₀) (isUFormula_quote φ₀)]
      exact ih v
  | @exs s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    show SatSigma (s₀ + 1) _ _ ↔ _
    rw [quote_ex_sentence, SatSigma.exs_iff]
    simp only [Semiformula.eval_ex]
    refine exists_congr fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp]
    exact ih (x :> v)
  | @all s₀ n₀ φ₀ hφ₀ ih =>
    intro v
    show SatPi (s₀ + 1) _ _ ↔ _
    rw [quote_all_sentence, SatPi.all_iff]
    simp only [Semiformula.eval_all]
    refine forall_congr' fun x ↦ ?_
    rw [show (x ∷ matrixToVec v : V) = matrixToVec (x :> v) by simp]
    exact ih (x :> v)

/-- For a strict prenex `Σₙ` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satSigma_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 n φ) (v : Fin k → V) :
    SatSigma n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := satClass_quote_iff hφ v

/-- For a strict prenex `Πₙ` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satPi_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚷 n φ) (v : Fin k → V) :
    SatPi n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := satClass_quote_iff hφ v

/-- The sentence asserting agreement of `φ` with its level-`Σₙ₊₁` partial truth definition.
- [HP98, Corollary I.1.76] -/
noncomputable def snowing (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* (φ 🡘 (satSigmaVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

/-- Semantic interpretation of the sentence `snowing n φ`: the substituted right-hand side is
the defining formula of `satSigmaVec`, read under the assignment given by the free variables.
- [HP98, Corollary I.1.76] -/
theorem models_snowing_iff {n k : ℕ} (φ : ArithmeticSemisentence k) :
    V↓[ℒₒᵣ] ⊧ snowing n φ ↔
      ∀ v : Fin k → V, V ⊧/v φ ↔ SatSigma (n + 1) ⌜φ⌝ (matrixToVec v) := by
  simp [snowing, models_iff, (satSigmaVec.defined n k).df, Function.comp_def]

/-- The theory form of the snowing lemma follows from `𝗣𝗔⁻` and the finite Tarski theory.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/
theorem provable_snowing_of_tarski {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗣𝗔⁻ ∪ tarski n ⊢ snowing n φ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ ∪ tarski n : ArithmeticTheory) :=
    Entailment.WeakerThan.trans (𝓣 := (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
      (Entailment.Axiomatized.le_of_subset Set.subset_union_left)
  refine Arithmetic.provable_iff_of_models_iff (T := (𝗣𝗔⁻ ∪ tarski n : ArithmeticTheory)) ?_
  intro M _ _ e
  have hPA : M↓[ℒₒᵣ] ⊧* (𝗣𝗔⁻ : ArithmeticTheory) :=
    Semantics.ModelsSet.of_subset (U := (𝗣𝗔⁻ ∪ tarski n : ArithmeticTheory)) inferInstance
      Set.subset_union_left
  have hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ := fun σ hσ ↦
    Semantics.ModelsSet.models (T := (𝗣𝗔⁻ ∪ tarski n : ArithmeticTheory)) _
      (Set.mem_union_right _ hσ)
  have := hPA
  have hkey : ∀ (p : M) (w : Fin k → M),
      M ⊧/(p :> w) (satSigmaVec n k).val ↔ ∃ ev, Codes w ev ∧ Reading.SatSig n p ev := by
    intro p w
    simp [satSigmaVec, Reading.Codes, Reading.Len, Reading.Nth, Reading.SatSig]
    done
  have hsub : M ⊧/e ((satSigmaVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))
      ↔ M ⊧/(((⌜φ⌝ : ℕ) : M) :> e) (satSigmaVec n k).val := by
    simp [Semiformula.eval_substs, Function.comp_def]
    done
  done

/-- `𝗜𝚺₁` proves the snowing sentence for every strict prenex `Σₙ₊₁` formula: the two sides
agree in every model of `𝗜𝚺₁` by `satSigma_quote_iff`, so completeness delivers a proof.
- [HP98, Corollary I.1.76] -/
theorem ISigma1.provable_snowing {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗜𝚺₁ ⊢ snowing n φ := by
  apply Arithmetic.complete.{0}
  intro M _ _
  exact (models_snowing_iff φ).mpr fun v ↦ (satSigma_quote_iff hφ v).symm


/-! ## The snowing lemma over `𝗣𝗔⁻`

The agreement above uses `𝗜𝚺₁` throughout: `SatZero` and `SatSigma` are functions of the model,
and the induction that drives `satZero_quote_iff` is the `𝚫₁` induction of `𝗜𝚺₁`. The consumer of
the snowing lemma needs a single finite theory that works for every `φ`, so the argument is
redone here over `𝗣𝗔⁻` together with the sentences of `tarski n`, where the satisfaction
predicates are visible only through those sentences. Both inductions become external inductions
on the formula `φ`.
-/

section peanoMinus

open Tarski Reading PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {n : ℕ}
  (hM : ∀ σ : ArithmeticSentence, tarski n σ → M↓[ℒₒᵣ] ⊧ σ)

/-! ### Coding facts about standard codes

Everything the argument needs to know about the code of a fixed formula or term is a true `𝚺₁`
statement about standard numbers, hence holds in `M` by `𝚺₁`-completeness of `𝗣𝗔⁻`. -/

/-- The code of a closed semiterm is a well-formed internal term.
- [HP98, 1.66] -/
private lemma uTerm_quote_cast {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) :
    UTerm ((⌜t⌝ : ℕ) : M) :=
  cast_delta₁ (isUTerm ℒₒᵣ) (by simpa using isUTerm_quote (V := ℕ) t)

/-- The code of a semisentence is a well-formed internal formula.
- [HP98, 1.66] -/
private lemma uFormula_quote_cast {k : ℕ} (φ : ArithmeticSemisentence k) :
    UFormula ((⌜φ⌝ : ℕ) : M) :=
  cast_delta₁ (isUFormula ℒₒᵣ) (by simpa using isUFormula_quote (V := ℕ) φ)

/-- The code of a bounded semisentence is internally `Δ₀`.
- [HP98, Lemma I.1.68] -/
private lemma delta0_quote_cast {k : ℕ} {φ : ArithmeticSemisentence k} (h : Hierarchy 𝚺 0 φ) :
    Delta0 ((⌜φ⌝ : ℕ) : M) :=
  cast_delta₁ isDelta0 (by simpa using (isDelta0_quote_iff (V := ℕ) φ).mpr h)

/-- The code of a strict prenex semisentence is in the matching internal strict class.
- [HP98, Lemma I.1.69] -/
private lemma strict_quote_cast {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) : Strict Γ s ((⌜φ⌝ : ℕ) : M) := by
  rcases Γ with _ | _
  · exact cast_delta₁ (isStrictSigma s) (by simpa using (isStrictSigma_quote_iff (V := ℕ) φ).mpr h)
  · exact cast_delta₁ (isStrictPi s) (by simpa using (isStrictPi_quote_iff (V := ℕ) φ).mpr h)

/-! ### Evaluation of coded closed terms -/

include hM in
/-- The value of the code of a closed semiterm, read through the term-evaluation sentences of
`tarski n`, is its value in the model.
- [HP98, 1.66] -/
private lemma termVal_quote_cast {k : ℕ} {v : Fin k → M} {ev : M} (hev : Codes v ev) :
    ∀ t : ClosedSemiterm ℒₒᵣ k, TermVal (t.valb v) ev ((⌜t⌝ : ℕ) : M) := by
  intro t
  induction t with
  | bvar i =>
    have hb : M ⊧/![((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M), ((i.val : ℕ) : M)] qqBvarDef.val :=
      cast_sigmaZero₂ qqBvarDef (by simpa using quote_bvar_sentence (V := ℕ) i)
    have := (read_termValBvar hM ev ((i.val : ℕ) : M) ((⌜(#i : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
      (v i) hb).mpr (hev.2 i)
    simpa using this
  | fvar x => exact x.elim
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      have hval : (Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k).valb v
          = 0 := rfl
      have hq : ((⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
          = ((𝟎 : ℕ) : M) := by
        rw [show (⌜(Semiterm.func Language.ORing.Func.zero w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟎 by
          simpa using quote_zeroTerm_sentence (V := ℕ) w]
      rw [hval, hq]
      exact (read_termValZero hM ev 0).mpr rfl
    | 0, .one, w, _ =>
      have hval : (Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k).valb v
          = 1 := rfl
      have hq : ((⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
          = ((𝟏 : ℕ) : M) := by
        rw [show (⌜(Semiterm.func Language.ORing.Func.one w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) = 𝟏 by
          simpa using quote_oneTerm_sentence (V := ℕ) w]
      rw [hval, hq]
      exact (read_termValOne hM ev 1).mpr rfl
    | 2, .add, w, ih =>
      have hval : (Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k).valb v
          = (w 0).valb v + (w 1).valb v := rfl
      have hq : M ⊧/![((⌜(Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqAddGraph.val :=
        cast_sigma₃ Arithmetic.qqAddGraph (by simpa using quote_addTerm_sentence (V := ℕ) w)
      rw [hval]
      exact (read_termValAdd hM ev ((⌜w 0⌝ : ℕ) : M) ((⌜w 1⌝ : ℕ) : M)
        ((⌜(Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
        ((w 0).valb v) ((w 1).valb v) ((w 0).valb v + (w 1).valb v)
        (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq (ih 0) (ih 1)).mpr rfl
    | 2, .mul, w, ih =>
      have hval : (Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k).valb v
          = (w 0).valb v * (w 1).valb v := rfl
      have hq : M ⊧/![((⌜(Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M),
          ((⌜w 0⌝ : ℕ) : M), ((⌜w 1⌝ : ℕ) : M)] Arithmetic.qqMulGraph.val :=
        cast_sigma₃ Arithmetic.qqMulGraph (by simpa using quote_mulTerm_sentence (V := ℕ) w)
      rw [hval]
      exact (read_termValMul hM ev ((⌜w 0⌝ : ℕ) : M) ((⌜w 1⌝ : ℕ) : M)
        ((⌜(Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : ℕ) : M)
        ((w 0).valb v) ((w 1).valb v) ((w 0).valb v * (w 1).valb v)
        (uTerm_quote_cast (w 0)) (uTerm_quote_cast (w 1)) hq (ih 0) (ih 1)).mpr rfl


/-! ### The `Δ₀` base case -/

include hM in
/-- Over `𝗣𝗔⁻` and the sentences of `tarski n`, the reading of `satZero` at the code of a bounded
formula agrees with truth. This is `satZero_quote_iff` again, with the `𝚫₁` induction of `𝗜𝚺₁`
replaced by the external induction on the bounded formula.
- [HP98, Theorem I.1.70]
- [HP98, Corollary I.1.76] -/
private lemma satZero_quote_reading {k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : Hierarchy 𝚺 0 φ) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev → (Sat0 ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  refine delta₀_induction (ξ := Empty)
    (P := fun k φ ↦ ∀ (v : Fin k → M) (ev : M), Codes v ev →
      (Sat0 ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k φ hφ
  · intro m v ev _
    have hq : M ⊧/![((⌜(⊤ : ArithmeticSemisentence m)⌝ : ℕ) : M)] qqVerumDef.val :=
      cast_sigmaZero₁ qqVerumDef (by simp [Sentence.quote_def])
    simpa using read_satZeroVerum hM _ ev hq
  · intro m v ev _
    have hq : M ⊧/![((⌜(⊥ : ArithmeticSemisentence m)⌝ : ℕ) : M)] qqFalsumDef.val :=
      cast_sigmaZero₁ qqFalsumDef (by simp [Sentence.quote_def])
    simpa using read_satZeroFalsum hM _ ev hq
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.rel Language.Eq.eq ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqEQDef.val :=
      cast_sigma₃ qqEQDef (by simpa using quote_eq_sentence (V := ℕ) t u)
    rw [read_satZeroEq hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_rel]
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.nrel Language.Eq.eq ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqNEQDef.val :=
      cast_sigma₃ qqNEQDef (by simpa using quote_neq_sentence (V := ℕ) t u)
    rw [read_satZeroNeq hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_nrel]
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.rel Language.LT.lt ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqLTDef.val :=
      cast_sigma₃ qqLTDef (by simpa using quote_lt_sentence (V := ℕ) t u)
    rw [read_satZeroLt hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_rel]
  · intro m t u v ev hev
    have hq : M ⊧/![((⌜(.nrel Language.LT.lt ![t, u] : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((⌜t⌝ : ℕ) : M), ((⌜u⌝ : ℕ) : M)] qqNLTDef.val :=
      cast_sigma₃ qqNLTDef (by simpa using quote_nlt_sentence (V := ℕ) t u)
    rw [read_satZeroNlt hM ((⌜t⌝ : ℕ) : M) ((⌜u⌝ : ℕ) : M) _ ev (t.valb v) (u.valb v)
      (uTerm_quote_cast t) (uTerm_quote_cast u) hq
      (termVal_quote_cast hM hev t) (termVal_quote_cast hM hev u)]
    simp [Semiformula.eval_nrel]
  · intro m φ ψ _ _ ihφ ihψ v ev hev
    have hq : M ⊧/![((⌜φ ⋏ ψ⌝ : ℕ) : M), ((⌜φ⌝ : ℕ) : M), ((⌜ψ⌝ : ℕ) : M)] qqAndDef.val :=
      cast_sigmaZero₃ qqAndDef (by simpa using quote_and_sentence (V := ℕ) φ ψ)
    rw [read_satZeroAnd hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev hq, ihφ v ev hev, ihψ v ev hev]
    simp
  · intro m φ ψ hφ hψ ihφ ihψ v ev hev
    have hq : M ⊧/![((⌜φ ⋎ ψ⌝ : ℕ) : M), ((⌜φ⌝ : ℕ) : M), ((⌜ψ⌝ : ℕ) : M)] qqOrDef.val :=
      cast_sigmaZero₃ qqOrDef (by simpa using quote_or_sentence (V := ℕ) φ ψ)
    rw [read_satZeroOr hM ((⌜φ⌝ : ℕ) : M) ((⌜ψ⌝ : ℕ) : M) _ ev
      (delta0_quote_cast hφ) (uFormula_quote_cast φ) (delta0_quote_cast hψ)
      (uFormula_quote_cast ψ) hq, ihφ v ev hev, ihψ v ev hev]
    simp
  · intro m t φ hφ ihφ v ev hev
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := cast_sigma₂ (termBShiftGraph ℒₒᵣ) (by simp)
    have hq : M ⊧/![((⌜(∀¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBallDef.val :=
      cast_sigma₃ qqBallDef (by simpa using quote_ball_sentence (V := ℕ) t φ)
    rw [read_satZeroBall hM ((⌜t⌝ : ℕ) : M) ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M)
      ((⌜φ⌝ : ℕ) : M) _ ev (t.valb v) (uTerm_quote_cast t) (delta0_quote_cast hφ)
      (uFormula_quote_cast φ) hu hq (termVal_quote_cast hM hev t)]
    simp only [Semiformula.eval_ball, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    constructor
    · intro h x hx
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact (ihφ (x :> v) e' (codes_cons hM hev hadj)).mp
        (h x (by simpa [Function.comp_def] using hx) e' hadj)
    · intro h x hx e' hadj
      exact (ihφ (x :> v) e' (codes_cons hM hev hadj)).mpr
        (by simpa [Function.comp_def] using h x (by simpa [Function.comp_def] using hx))
  · intro m t φ hφ ihφ v ev hev
    have hu : M ⊧/![((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜t⌝ : ℕ) : M)]
        (termBShiftGraph ℒₒᵣ).val := cast_sigma₂ (termBShiftGraph ℒₒᵣ) (by simp)
    have hq : M ⊧/![((⌜(∃¹[“#0 < !!(Rew.bShift t)”] φ : ArithmeticSemisentence m)⌝ : ℕ) : M),
        ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M), ((⌜φ⌝ : ℕ) : M)] qqBexDef.val :=
      cast_sigma₃ qqBexDef (by simpa using quote_bex_sentence (V := ℕ) t φ)
    rw [read_satZeroBex hM ((⌜t⌝ : ℕ) : M) ((termBShift ℒₒᵣ (⌜t⌝ : ℕ) : ℕ) : M)
      ((⌜φ⌝ : ℕ) : M) _ ev (t.valb v) (uTerm_quote_cast t) hu hq
      (termVal_quote_cast hM hev t)]
    simp only [Semiformula.eval_bexs, Semiformula.Operator.lt_def, Semiformula.eval_rel]
    constructor
    · rintro ⟨x, hx, e', hadj, hsat⟩
      exact ⟨x, by simpa [Function.comp_def] using hx,
        (ihφ (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩
    · rintro ⟨x, hx, hsat⟩
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact ⟨x, by simpa [Function.comp_def] using hx, e', hadj,
        (ihφ (x :> v) e' (codes_cons hM hev hadj)).mpr (by simpa [Function.comp_def] using hsat)⟩

/-! ### The strict prenex induction -/

include hM in
/-- Over `𝗣𝗔⁻` and the sentences of `tarski n`, the reading of the level-`s` satisfaction formula
at the code of a strict prenex formula agrees with truth. This is `satClass_quote_iff` again,
carried out with the finitely many Tarski sentences in place of the satisfaction predicates.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/
private lemma satClass_quote_reading {Γ : Polarity} {s k : ℕ} {φ : ArithmeticSemisentence k}
    (h : StrictHierarchy Γ s φ) (hs : s ≤ n) :
    ∀ (v : Fin k → M) (ev : M), Codes v ev → (Sat Γ s ((⌜φ⌝ : ℕ) : M) ev ↔ M ⊧/v φ) := by
  revert hs
  induction h with
  | @zero Γ₀ m₀ φ₀ hφ₀ =>
    intro _ v ev hev
    exact satZero_quote_reading hM hφ₀ v ev hev
  | @ofAlt Γ₀ s₀ m₀ φ₀ hφ₀ ih =>
    intro hs v ev hev
    rw [read_ofAlt hM (show s₀ ≤ n by omega) Γ₀ ((⌜φ₀⌝ : ℕ) : M) ev
      (strict_quote_cast hφ₀) (uFormula_quote_cast φ₀)]
    exact ih (by omega) v ev hev
  | @exs s₀ m₀ φ₀ _ ih =>
    intro hs v ev hev
    have hq : M ⊧/![((⌜(∃¹ φ₀ : ArithmeticSemisentence m₀)⌝ : ℕ) : M), ((⌜φ₀⌝ : ℕ) : M)]
        qqExsDef.val := cast_sigmaZero₂ qqExsDef (by simpa using quote_ex_sentence (V := ℕ) φ₀)
    show Reading.SatSig s₀ _ _ ↔ _
    rw [read_satSigmaExs hM (show s₀ ≤ n by omega) ((⌜φ₀⌝ : ℕ) : M) _ ev hq]
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨x, e', hadj, hsat⟩
      exact ⟨x, (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mp hsat⟩
    · rintro ⟨x, hsat⟩
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact ⟨x, e', hadj, (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mpr hsat⟩
  | @all s₀ m₀ φ₀ _ ih =>
    intro hs v ev hev
    have hq : M ⊧/![((⌜(∀¹ φ₀ : ArithmeticSemisentence m₀)⌝ : ℕ) : M), ((⌜φ₀⌝ : ℕ) : M)]
        qqAllDef.val := cast_sigmaZero₂ qqAllDef (by simpa using quote_all_sentence (V := ℕ) φ₀)
    show Reading.SatPii s₀ _ _ ↔ _
    rw [read_satPiAll hM (show s₀ ≤ n by omega) ((⌜φ₀⌝ : ℕ) : M) _ ev hq]
    simp only [Semiformula.eval_all]
    constructor
    · intro hsat x
      obtain ⟨e', hadj⟩ := read_adjoinTotal hM x ev
      exact (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mp (hsat x e' hadj)
    · intro hsat x e' hadj
      exact (ih (by omega) (x :> v) e' (codes_cons hM hev hadj)).mpr (hsat x)

end peanoMinus


end LO.FirstOrder.Arithmetic
