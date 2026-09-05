module

public import AlphaCentauri.Bootstrapping.PartialTruth.SatSigma

/-!
# Partial truth definitions agree with truth

This module states the “it's snowing” agreement between partial satisfaction and semantics.
It also packages the required Tarski conditions as an explicit finite arithmetic theory.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Codes of quoted semisentences

Foundation's `quote_*` lemmas compute the code of a `Semiproposition`. A `Semisentence` is
quoted through its embedding (`Sentence.quote_def`), so each of them has a counterpart here. -/

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

/-! ## Agreement of satisfaction with truth -/

/-- For a bounded formula, internal `Δ₀` satisfaction of its code agrees with truth.
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

/-- The satisfaction predicate selected by a polarity: `SatSigma` for `Σ`, `SatPi` for `Π`.
- [HP98, Definition I.1.74] -/
def SatClass : Polarity → ℕ → V → V → Prop
  | .sigma, n, z, e => SatSigma n z e
  | .pi, n, z, e => SatPi n z e

/-- Internal satisfaction of the code of a strict prenex formula agrees with truth.
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

/-- For a strict prenex `𝚺-[n]` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satSigma_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 n φ) (v : Fin k → V) :
    SatSigma n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := satClass_quote_iff hφ v

/-- For a strict prenex `𝚷-[n]` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satPi_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚷 n φ) (v : Fin k → V) :
    SatPi n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := satClass_quote_iff hφ v

/-- The sentence asserting agreement of `φ` with its level-`𝚺-[n + 1]` partial truth definition.
- [HP98, Corollary I.1.76] -/
noncomputable def snowing (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* (φ 🡘 (satSigmaVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

/-- Semantic characterization of the sentence `snowing n φ`.
- [HP98, Corollary I.1.76] -/
theorem models_snowing_iff {n k : ℕ} (φ : ArithmeticSemisentence k) :
    V↓[ℒₒᵣ] ⊧ snowing n φ ↔
      ∀ v : Fin k → V, V ⊧/v φ ↔ SatSigma (n + 1) ⌜φ⌝ (matrixToVec v) := by
  simp [snowing, models_iff, (satSigmaVec.defined n k).df, Function.comp_def]

/-! ## Tarski conditions as sentences -/

namespace Tarski

/-- Satisfaction is restricted to internally coded `Δ₀` formulas.
- [HP98, Theorem I.1.70(i)] -/
noncomputable def satZeroDom : ArithmeticSentence :=
  “∀ z e, !satZero.val z e → !isDelta0.val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The Tarski sentence for truth.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroVerum : ArithmeticSentence :=
  “∀ z e, !qqVerumDef.val z → !satZero.val z e”

/-- The Tarski sentence for falsehood.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroFalsum : ArithmeticSentence :=
  “∀ z e, !qqFalsumDef.val z → ¬!satZero.val z e”

/-- The Tarski sentence for equality.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroEq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ vt = vu)”

/-- The Tarski sentence for inequality.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroNeq : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNEQDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ vt ≠ vu)”

/-- The Tarski sentence for less-than.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroLt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ vt < vu)”

/-- The Tarski sentence for negated less-than.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroNlt : ArithmeticSentence :=
  “∀ t u z e vt vu, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !qqNLTDef.val z t u → !termValGraph.val vt e t → !termValGraph.val vu e u →
    (!satZero.val z e ↔ ¬(vt < vu))”

/-- The Tarski sentence for conjunction.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroAnd : ArithmeticSentence :=
  “∀ p q z e, !qqAndDef.val z p q →
    (!satZero.val z e ↔ !satZero.val p e ∧ !satZero.val q e)”

/-- The Tarski sentence for disjunction.
- [HP98, Theorem I.1.70(ii)] -/
noncomputable def satZeroOr : ArithmeticSentence :=
  “∀ p q z e, !qqOrDef.val z p q →
    (!satZero.val z e ↔ !satZero.val p e ∨ !satZero.val q e)”

/-- The Tarski sentence for negation.
- [HP98, Theorem I.1.70(iii)] -/
noncomputable def satZeroNeg : ArithmeticSentence :=
  “∀ p np e, !isDelta0.val p → !(isUFormula ℒₒᵣ).val p →
    !(negGraph ℒₒᵣ).val np p → (!satZero.val np e ↔ ¬!satZero.val p e)”

/-- The Tarski sentence for bounded universal quantification.
- [HP98, Theorem I.1.70(iv)] -/
noncomputable def satZeroBall : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !isDelta0.val q →
    !(isUFormula ℒₒᵣ).val q → !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBallDef.val z u q → !termValGraph.val v e t →
    (!satZero.val z e ↔ ∀ x < v, ∀ e', !adjoinDef.val e' x e → !satZero.val q e')”

/-- The Tarski sentence for bounded existential quantification.
- [HP98, Theorem I.1.70(iv)] -/
noncomputable def satZeroBex : ArithmeticSentence :=
  “∀ t u q z e v, !(isUTerm ℒₒᵣ).val t → !(termBShiftGraph ℒₒᵣ).val u t →
    !qqBexDef.val z u q → !termValGraph.val v e t →
    (!satZero.val z e ↔ ∃ x < v, ∃ e', !adjoinDef.val e' x e ∧ !satZero.val q e')”

/-- The defining sentence for evaluation of coded bound variables.
- [HP98, 1.64(5)] -/
noncomputable def termValBvar : ArithmeticSentence :=
  “∀ e z t v, !qqBvarDef.val t z → (!termValGraph.val v e t ↔ !nthDef.val v e z)”

/-- The defining sentence for evaluation of zero.
- [HP98, 1.64(5)] -/
noncomputable def termValZero : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Bootstrapping.Arithmetic.zero ↔ v = 0”

/-- The defining sentence for evaluation of one.
- [HP98, 1.64(5)] -/
noncomputable def termValOne : ArithmeticSentence :=
  “∀ e v, !termValGraph.val v e ↑Bootstrapping.Arithmetic.one ↔ v = 1”

/-- The defining sentence for evaluation of addition.
- [HP98, 1.64(5)] -/
noncomputable def termValAdd : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Bootstrapping.Arithmetic.qqAddGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt + vu)”

/-- The defining sentence for evaluation of multiplication.
- [HP98, 1.64(5)] -/
noncomputable def termValMul : ArithmeticSentence :=
  “∀ e t u s vt vu v, !(isUTerm ℒₒᵣ).val t → !(isUTerm ℒₒᵣ).val u →
    !Bootstrapping.Arithmetic.qqMulGraph.val s t u → !termValGraph.val vt e t →
    !termValGraph.val vu e u →
    (!termValGraph.val v e s ↔ v = vt * vu)”

/-- Coded vector adjunction is total.
- No source; an elementary vector-coding lemma. -/
noncomputable def adjoinTotal : ArithmeticSentence :=
  “∀ x v, ∃ e, !adjoinDef.val e x v”

/-- Coded vector adjunction is functional.
- No source; an elementary vector-coding lemma. -/
noncomputable def adjoinUnique : ArithmeticSentence :=
  “∀ x v e e', !adjoinDef.val e x v → !adjoinDef.val e' x v → e = e'”

/-- The head of an adjoined coded vector is its new entry.
- No source; an elementary vector-coding lemma. -/
noncomputable def nthAdjoinZero : ArithmeticSentence :=
  “∀ x v e y, !adjoinDef.val e x v → (!nthDef.val y e 0 ↔ y = x)”

/-- Successor indices into an adjoined coded vector read from its tail.
- No source; an elementary vector-coding lemma. -/
noncomputable def nthAdjoinSucc : ArithmeticSentence :=
  “∀ x v e i y, !adjoinDef.val e x v →
    (!nthDef.val y e (i + 1) ↔ !nthDef.val y v i)”

/-- The empty coded vector has length zero.
- No source; an elementary vector-coding lemma. -/
noncomputable def lenNil : ArithmeticSentence := “∀ l, !lenDef.val l 0 ↔ l = 0”

/-- Adjunction increases the length of a coded vector by one.
- No source; an elementary vector-coding lemma. -/
noncomputable def lenAdjoin : ArithmeticSentence :=
  “∀ x v e l, !adjoinDef.val e x v → (!lenDef.val (l + 1) e ↔ !lenDef.val l v)”

/-- The empty-block Tarski condition for reading `𝚷-[n]` satisfaction as `𝚺-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaOfPi : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictPi (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma (n + 1)).val z e ↔ !(satPi n).val z e)”

/-- The empty-block Tarski condition for reading `𝚺-[n]` satisfaction as `𝚷-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiOfSigma : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi (n + 1)).val z e ↔ !(satSigma n).val z e)”

/-- The domain Tarski condition for `𝚺-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satSigmaDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satSigma n).val z e →
    !(isStrictSigma (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The domain Tarski condition for `𝚷-[n + 1]` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satPi n).val z e →
    !(isStrictPi (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The Tarski condition for existential quantification at level `𝚺-[n + 1]`.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaExs (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqExsDef.val z p →
    (!(satSigma n).val z e ↔
      ∃ x e', !adjoinDef.val e' x e ∧ !(satSigma n).val p e')”

/-- The Tarski condition for universal quantification at level `𝚷-[n + 1]`.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiAll (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqAllDef.val z p →
    (!(satPi n).val z e ↔
      ∀ x e', !adjoinDef.val e' x e → !(satPi n).val p e')”

/-- The negation-duality Tarski condition from `𝚺-[n + 1]` to `𝚷-[n + 1]`.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(satPi n).val nz e ↔ ¬!(satSigma n).val z e)”

/-- The negation-duality Tarski condition from `𝚷-[n + 1]` to `𝚺-[n + 1]`.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satSigmaNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictPi (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(satSigma n).val nz e ↔ ¬!(satPi n).val z e)”

/-- The finite collection of `Δ₀` Tarski and term-evaluation sentences.
- [HP98, Theorem I.1.70]
- [HP98, Remark I.1.77] -/
noncomputable def satZeroAxioms : ArithmeticTheory :=
  {satZeroDom, satZeroVerum, satZeroFalsum, satZeroEq, satZeroNeq, satZeroLt,
    satZeroNlt, satZeroAnd, satZeroOr, satZeroNeg, satZeroBall, satZeroBex,
    termValBvar, termValZero, termValOne, termValAdd, termValMul, adjoinTotal,
    adjoinUnique, nthAdjoinZero, nthAdjoinSucc, lenNil, lenAdjoin}

/-- The finite collection of level-`n + 1` Tarski sentences.
- [HP98, Theorem I.1.75(2)]
- [HP98, Remark I.1.77] -/
noncomputable def satSigmaAxioms (n : ℕ) : ArithmeticTheory :=
  {satSigmaOfPi n, satPiOfSigma n, satSigmaDom n, satPiDom n, satSigmaExs n,
    satPiAll n, satPiNeg n, satSigmaNeg n}

end Tarski

/-- `tarski n` contains the Tarski, vector, and term-evaluation conditions through level `n + 1`.
- [HP98, Remark I.1.77] -/
inductive tarski : ℕ → ArithmeticTheory
  | zero : ∀ φ ∈ Tarski.satZeroAxioms, tarski 0 φ
  | prev : ∀ n φ, tarski n φ → tarski (n + 1) φ
  | new  : ∀ n, ∀ φ ∈ Tarski.satSigmaAxioms n, tarski (n + 1) φ

/-- The explicit Tarski theory at each level is finite.
- [HP98, Remark I.1.77] -/
lemma tarski_finite (n : ℕ) : (tarski n).Finite := by
  induction n with
  | zero =>
    have e : tarski 0 = Tarski.satZeroAxioms := by
      ext φ; constructor
      · rintro ⟨⟩; assumption
      · exact tarski.zero φ
    rw [e]; simp only [Tarski.satZeroAxioms]; exact Set.toFinite _
  | succ n ih =>
    have e : tarski (n + 1) = tarski n ∪ Tarski.satSigmaAxioms n := by
      ext φ; constructor
      · rintro (⟨⟩ | ⟨⟩)
        · exact Or.inl ‹tarski n φ›
        · exact Or.inr ‹φ ∈ Tarski.satSigmaAxioms n›
      · rintro (h | h)
        · exact tarski.prev n φ h
        · exact tarski.new n φ h
    rw [e]
    refine ih.union ?_
    simp only [Tarski.satSigmaAxioms]; exact Set.toFinite _

/-- `𝗜𝚺₁` proves every sentence in the finite Tarski theory.
- [HP98, Theorem I.1.70]
- [HP98, Theorem I.1.75(2)]
- [HP98, Remark I.1.77] -/
axiom ISigma1.provable_tarski (n : ℕ) : 𝗜𝚺₁ ⊢* tarski n

/-- `𝗣𝗔⁻` together with the finite Tarski theory proves the snowing lemma.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/
axiom provable_snowing_of_tarski {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗣𝗔⁻ ∪ tarski n ⊢ snowing n φ

/-- `𝗜𝚺₁` proves the snowing sentence for every strict prenex `𝚺-[n + 1]` formula.
- [HP98, Corollary I.1.76] -/
theorem ISigma1.provable_snowing {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗜𝚺₁ ⊢ snowing n φ := by
  apply Arithmetic.complete.{0}
  intro M _ _
  exact (models_snowing_iff φ).mpr fun v ↦ (satSigma_quote_iff hφ v).symm

end LO.FirstOrder.Arithmetic
