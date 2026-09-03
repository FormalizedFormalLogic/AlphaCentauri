module

public import AlphaCentauri.FirstOrder.Incompleteness.PartialTruth.SatSigma

/-!
# Partial truth definitions agree with truth

This module states the “it's snowing” agreement between partial satisfaction and semantics.
It also packages the required Tarski conditions as an explicit finite arithmetic theory.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For a strict prenex `Σₙ` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satSigma_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 n φ) (v : Fin k → V) :
    SatSigma n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := sorry

/-- For a strict prenex `Πₙ` formula, internal satisfaction of its code agrees with truth.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.80] -/
theorem satPi_quote_iff {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚷 n φ) (v : Fin k → V) :
    SatPi n ⌜φ⌝ (matrixToVec v) ↔ V ⊧/v φ := sorry

/-- The sentence asserting agreement of `φ` with its level-`Σₙ₊₁` partial truth definition.
- [HP98, Corollary I.1.76] -/
noncomputable def snowing (n : ℕ) {k : ℕ}
    (φ : ArithmeticSemisentence k) : ArithmeticSentence :=
  ∀¹* (φ 🡘 (satSigmaVec n k).val ⇜ ((⌜φ⌝ : ArithmeticSemiterm Empty k) :> fun i ↦ #i))

/-- Semantic interpretation of the sentence `snowing n φ`.
- [HP98, Corollary I.1.76] -/
lemma models_snowing_iff {n k : ℕ} (φ : ArithmeticSemisentence k) :
    V↓[ℒₒᵣ] ⊧ snowing n φ ↔
      ∀ v : Fin k → V, V ⊧/v φ ↔ SatSigma (n + 1) ⌜φ⌝ (matrixToVec v) := sorry

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
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def adjoinTotal : ArithmeticSentence :=
  “∀ x v, ∃ e, !adjoinDef.val e x v”

/-- Coded vector adjunction is functional.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def adjoinUnique : ArithmeticSentence :=
  “∀ x v e e', !adjoinDef.val e x v → !adjoinDef.val e' x v → e = e'”

/-- The head of an adjoined coded vector is its new entry.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def nthAdjoinZero : ArithmeticSentence :=
  “∀ x v e y, !adjoinDef.val e x v → (!nthDef.val y e 0 ↔ y = x)”

/-- Successor indices into an adjoined coded vector read from its tail.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def nthAdjoinSucc : ArithmeticSentence :=
  “∀ x v e i y, !adjoinDef.val e x v →
    (!nthDef.val y e (i + 1) ↔ !nthDef.val y v i)”

/-- The empty coded vector has length zero.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def lenNil : ArithmeticSentence := “∀ l, !lenDef.val l 0 ↔ l = 0”

/-- Adjunction increases the length of a coded vector by one.
- No source; this is a routine vector-coding fact used in the snowing argument. -/
noncomputable def lenAdjoin : ArithmeticSentence :=
  “∀ x v e l, !adjoinDef.val e x v → (!lenDef.val (l + 1) e ↔ !lenDef.val l v)”

/-- The empty-block Tarski condition for reading `Πₙ` satisfaction as `Σₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaOfPi : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictPi (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satSigma (n + 1)).val z e ↔ !(satPi n).val z e)”

/-- The empty-block Tarski condition for reading `Σₙ` satisfaction as `Πₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiOfSigma : ℕ → ArithmeticSentence
  | 0 =>
      “∀ z e, !isDelta0.val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi 0).val z e ↔ !satZero.val z e)”
  | n + 1 =>
      “∀ z e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
        (!(satPi (n + 1)).val z e ↔ !(satSigma n).val z e)”

/-- The domain Tarski condition for `Σₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satSigmaDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satSigma n).val z e →
    !(isStrictSigma (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The domain Tarski condition for `Πₙ₊₁` satisfaction.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiDom (n : ℕ) : ArithmeticSentence :=
  “∀ z e, !(satPi n).val z e →
    !(isStrictPi (n + 1)).val z ∧ !(isUFormula ℒₒᵣ).val z”

/-- The Tarski condition for existential quantification at level `Σₙ₊₁`.
- [HP98, Theorem I.1.75(2)(v)] -/
noncomputable def satSigmaExs (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqExsDef.val z p →
    (!(satSigma n).val z e ↔
      ∃ x e', !adjoinDef.val e' x e ∧ !(satSigma n).val p e')”

/-- The Tarski condition for universal quantification at level `Πₙ₊₁`.
- [HP98, Theorem I.1.75(2)(v′)] -/
noncomputable def satPiAll (n : ℕ) : ArithmeticSentence :=
  “∀ p z e, !qqAllDef.val z p →
    (!(satPi n).val z e ↔
      ∀ x e', !adjoinDef.val e' x e → !(satPi n).val p e')”

/-- The negation-duality Tarski condition from `Σₙ₊₁` to `Πₙ₊₁`.
- [HP98, Theorem I.1.75(2)] -/
noncomputable def satPiNeg (n : ℕ) : ArithmeticSentence :=
  “∀ z nz e, !(isStrictSigma (n + 1)).val z → !(isUFormula ℒₒᵣ).val z →
    !(negGraph ℒₒᵣ).val nz z →
    (!(satPi n).val nz e ↔ ¬!(satSigma n).val z e)”

/-- The negation-duality Tarski condition from `Πₙ₊₁` to `Σₙ₊₁`.
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

/-- `tarski n` contains the finitely many Tarski conditions through level `n + 1`, together
with the vector and term-evaluation facts used in the proof of the snowing lemma. Its exact
membership may grow during the proof stage; downstream arguments use only finiteness and
`𝗜𝚺₁`-provability.

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
theorem ISigma1.provable_tarski (n : ℕ) : 𝗜𝚺₁ ⊢* tarski n := sorry

/-- The theory form of the snowing lemma follows from `𝗣𝗔⁻` and the finite Tarski theory.
- [HP98, Corollary I.1.76]
- [HP98, Remark I.1.77] -/
theorem provable_snowing_of_tarski {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗣𝗔⁻ ∪ tarski n ⊢ snowing n φ := sorry

/-- `𝗜𝚺₁` proves the snowing sentence for every strict prenex `Σₙ₊₁` formula.
- [HP98, Corollary I.1.76] -/
theorem ISigma1.provable_snowing {n k : ℕ} {φ : ArithmeticSemisentence k}
    (hφ : StrictHierarchy 𝚺 (n + 1) φ) : 𝗜𝚺₁ ⊢ snowing n φ := sorry

end LO.FirstOrder.Arithmetic
